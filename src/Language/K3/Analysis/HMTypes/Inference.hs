{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Hindley-Milner type inference.
--
--   For K3, this does not support subtyping, nor does it check annotation
--   composition. Instead it treats annotated collections as ad-hoc external types,
--   and requires structural type equality to hold on function application.
--   Both of these functionalities are not required for K3-Mosaic code.
--
--   Most of the scaffolding is taken from Oleg Kiselyov's tutorial:
--   http://okmij.org/ftp/Computation/FLOLAC/TInfLetP.hs
--

-- TODO: add mutability annotations to tbvar
--       deal with mutability outside of unify
-- TODO: add uids to type variables and print them
-- TODO: deal with contravariance for functions passed in
-- TODO: keep most varids one level deep (pointing to another id that has a type) to improve performance
-- TODO: between lambda borders, we want to unify without forcing lowerbound expansion of types
--       and keep track of the connection for concretization
-- TODO: convert twlowers to regular types
-- TODO: widening phase
-- TODO: make sure we chase pointers anywhere where we pattern match
-- TODO: make sure we use unifyMWithVariableReplace where needed
-- TODO: print out uids

module Language.K3.Analysis.HMTypes.Inference where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Arrow (first, second, (&&&))

import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Hashable(Hashable)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Tree

import Debug.Trace

import Language.K3.Core.Annotation
import Language.K3.Core.Common
import Language.K3.Core.Declaration
import Language.K3.Core.Expression
import Language.K3.Core.Type
import Language.K3.Core.Constructor.Type as TC
import Language.K3.Analysis.Common
import Language.K3.Analysis.HMTypes.DataTypes
import Language.K3.Utils.Pretty

-- | Misc. helpers
(.+) :: K3 Expression -> K3 QType -> K3 Expression
(.+) e qt = e @+ (EQType $ mutabilityE e qt)

infixr 5 .+

immutQT :: K3 QType -> K3 QType
immutQT = (@+ QTImmutable)

mutQT :: K3 QType -> K3 QType
mutQT = (@+ QTMutable)

mutabilityT :: K3 Type -> K3 QType -> K3 QType
mutabilityT t qt = maybe propagate (const qt) $ find isQTQualified $ annotations qt
  where propagate = case t @~ isTQualified of
          Nothing -> qt
          Just TImmutable -> immutQT qt
          Just TMutable   -> mutQT qt
          _ -> error "Invalid type qualifier annotation"

mutabilityE :: K3 Expression -> K3 QType -> K3 QType
mutabilityE e qt = maybe propagate (const qt) $ find isQTQualified $ annotations qt
  where propagate = case e @~ isEQualified of
          Nothing -> qt
          Just EImmutable -> immutQT qt
          Just EMutable   -> mutQT qt
          _ -> error "Invalid expression qualifier annotation"

qTypeOf :: K3 Expression -> Maybe (K3 QType)
qTypeOf e = case e @~ isEQType of
              Just (EQType qt) -> Just qt
              _ -> Nothing

qTypeOfM :: K3 Expression -> TInfM (K3 QType)
qTypeOfM e = case e @~ isEQType of
              Just (EQType qt) -> return qt
              _ -> left $ "Untyped expression: " ++ show e

-- Get only the values matching keys among identifiers
projectNamedPairs :: [Identifier] -> [(Identifier, a)] -> [a]
projectNamedPairs ids idv = snd $ unzip $ filter (\(k,_) -> k `elem` ids) idv

-- Rearrange named pairs according to identifier list
-- We expect all the identifiers to be in idv
shuffleNamedPairs :: [Identifier] -> [(Identifier, a)] -> Maybe [a]
shuffleNamedPairs ids idv =
  let m = HashMap.fromList idv
  in mapM (`HashMap.lookup` m) ids

-- Replace matching values in newIds newVs if there's an id match
rebuildNamedPairs :: [(Identifier, a)] -> [Identifier] -> [a] -> [a]
rebuildNamedPairs oldIdv newIds newVs = map (replaceNewPair $ zip newIds newVs) oldIdv
  where replaceNewPair pairs (k,v) = fromMaybe v $ lookup k pairs

data QPLifted = QPLifted | QPUnlifted deriving (Eq, Read, Show)

isLifted :: QPLifted -> Bool
isLifted QPLifted   = True
isLifted QPUnlifted = False

-- | A type environment.
--   The first entry is the latest binding of the identifier
type TEnv = HashMap Identifier [QPType]

-- | Annotation member environment.
--   The boolean indicates whether the member is a lifted attribute.
type TMEnv = HashMap Identifier (QPType, QPLifted)

-- | Annotation type environment.
type TAEnv = HashMap Identifier TMEnv

-- | Declared type variable environment.
--   (Alwyas has a varId)
type TDVEnv = HashMap Identifier QTVarId

-- | A type variable allocation environment
--   1. the last assigned id
--   2. map of id to uid
type TVEnv = (QTVarId, IntMap (UID, Maybe Span))

-- | A type variable binding environment.
--   1. map of id to type/other id
type TVBEnv = IntMap (K3 QType)

-- | A concretization environment
--   Shows which types are applied to which other types, which must therefore
--   be their subtypes. Concretization will use this as a shortcut.
type TCEnv = IntMap IntSet

-- | A type inference environment.
data TIEnv = TIEnv {
               typeEnv     :: TEnv,
               annotEnv    :: TAEnv,
               declEnv     :: TDVEnv,
               tvarEnv     :: TVEnv,
               tvarBindEnv :: TVBEnv,
               concEnv     :: TCEnv
             }

-- | The type inference monad
type TInfM = EitherT String (State TIEnv)

{- TEnv helpers -}
-- TEnv is the identifier environment
tenv0 :: TEnv
tenv0 = HashMap.empty

tlkup :: TEnv -> Identifier -> Either String QPType
tlkup env x = maybe err (Right . head) $ HashMap.lookup x env
 where err = Left $ "Unbound variable in type environment: " ++ x

text :: TEnv -> Identifier -> QPType -> TEnv
-- We insertWith applies new `f` old, so we're fine
text env k qt = HashMap.insertWith (++) k [qt] env

tdel :: TEnv -> Identifier -> TEnv
tdel env x = case HashMap.lookup x env of
               Nothing     -> env
               Just []     -> HashMap.delete x env
               Just [_]    -> HashMap.delete x env
               Just (_:ls) -> HashMap.insert x ls env

-- TAEnv helpers
-- Annotation Environment
taenv0 :: TAEnv
taenv0 = HashMap.empty

talkup :: TAEnv -> Identifier -> Either String TMEnv
talkup env x = maybe err Right $ HashMap.lookup x env
  where err = Left $ "Unbound variable in annotation environment: " ++ x

taext :: TAEnv -> Identifier -> TMEnv -> TAEnv
taext env x te = HashMap.insert x te env


-- TDVEnv helpers
-- Declared type variable environment
tdvenv0 :: TDVEnv
tdvenv0 = HashMap.empty

tdvlkup :: TDVEnv -> Identifier -> Either String (K3 QType)
tdvlkup env x = maybe err (Right . tvar) $ HashMap.lookup x env
  where err = Left $ "Unbound declared variable in environment: " ++ x

tdvext :: TDVEnv -> Identifier -> QTVarId -> TDVEnv
tdvext env x v = HashMap.insert x v env

tdvdel :: TDVEnv -> Identifier -> TDVEnv
tdvdel env x = HashMap.delete x env

-- TCEnv helpers --
-- Concretization environment
tcenv0 :: TCEnv
tcenv0 = IntMap.empty

tclkup :: TCEnv -> QTVarId -> Maybe IntSet
tclkup env id' = IntMap.lookup id' env

tclext :: TCEnv -> QTVarId -> QTVarId -> TCEnv
tclext env id' id'' = IntMap.insertWith IntSet.union id' (IntSet.singleton id'') env

-- TVBEnv helpers
-- Type variable binding environment
tvbenv0 :: TVBEnv
tvbenv0 = IntMap.empty

tvblkup :: TVBEnv -> QTVarId -> Maybe (K3 QType)
tvblkup env v = IntMap.lookup v env

tvbext :: TVBEnv -> QTVarId -> K3 QType -> TVBEnv
tvbext env v t = IntMap.insert v t env


-- TVEnv helpers
-- Type Variable environment
tvenv0 :: TVEnv
tvenv0 = (0, IntMap.empty)

tvext :: TVEnv -> QTVarId -> UID -> Maybe Span -> TVEnv
tvext env v uid mspan = second (IntMap.insert v (uid, mspan)) env

tvinc :: TVEnv -> (QTVarId, TVEnv)
tvinc env =
  let env' = first (1 +) env
  in (fst env', env')

tvlkup :: TVEnv -> QTVarId -> (Maybe UID, Maybe Span)
tvlkup env v = maybe (Nothing, Nothing) (first Just) $ IntMap.lookup v $ snd env

{- TIEnv helpers -}
-- Full environment
tienv0 :: TIEnv
tienv0 = TIEnv tenv0 taenv0 tdvenv0 tvenv0 tvbenv0 tcenv0

-- | Modifiers.
modTypeEnv :: (TEnv -> TEnv) -> TIEnv -> TIEnv
modTypeEnv f env = env { typeEnv=f $ typeEnv env}

modAnnotEnv :: (TAEnv -> TAEnv) -> TIEnv -> TIEnv
modAnnotEnv f env = env { annotEnv=f $ annotEnv env}

modDeclEnv :: (TDVEnv -> TDVEnv) -> TIEnv -> TIEnv
modDeclEnv f env = env { declEnv=f $ declEnv env}

modTvarEnv :: (TVEnv -> TVEnv) -> TIEnv -> TIEnv
modTvarEnv f env = env { tvarEnv=f $ tvarEnv env}

modTvarBindEnv :: (TVBEnv -> TVBEnv) -> TIEnv -> TIEnv
modTvarBindEnv f env = env { tvarBindEnv=f $ tvarBindEnv env}

modConcEnv :: (TCEnv -> TCEnv) -> TIEnv -> TIEnv
modConcEnv f env = env { concEnv = f $ concEnv env}

tilkupe :: TIEnv -> Identifier -> Either String QPType
tilkupe env = tlkup $ typeEnv env

tilkupa :: TIEnv -> Identifier -> Either String TMEnv
tilkupa env = talkup $ annotEnv env

tilkupdv :: TIEnv -> Identifier -> Either String (K3 QType)
tilkupdv env = tdvlkup $ declEnv env

tiexte :: TIEnv -> Identifier -> QPType -> TIEnv
tiexte env x t = env {typeEnv=text (typeEnv env) x t}

tiexta :: TIEnv -> Identifier -> TMEnv -> TIEnv
tiexta env x ate = env {annotEnv=taext (annotEnv env) x ate}

tiextdv :: TIEnv -> Identifier -> QTVarId -> TIEnv
tiextdv env x v = env {declEnv=tdvext (declEnv env) x v}

tidele :: TIEnv -> Identifier -> TIEnv
tidele env i = env {typeEnv=tdel (typeEnv env) i}

tideldv :: TIEnv -> Identifier -> TIEnv
tideldv env i = env {declEnv=tdvdel (declEnv env) i}

-- General Utilities

-- Accurate subset calculation
subsetOf :: (Hashable a, Eq a) => [a] -> [a] -> Bool
subsetOf a b =
  let a' = HashSet.fromList a
      x  = a' `HashSet.intersection` HashSet.fromList b
  in x == a'

intersection :: (Hashable a, Eq a) => [a] -> [a] -> [a]
intersection a b = HashSet.toList $
                     HashSet.fromList a `HashSet.intersection` HashSet.fromList b

difference :: (Hashable a, Eq a) => [a] -> [a] -> [a]
difference a b = HashSet.toList $ HashSet.fromList a `HashSet.difference` HashSet.fromList b

-- Get the complete difference between 2 sets
diff2way :: (Hashable a, Eq a) => [a] -> [a] -> [a]
diff2way a b =
  let (a', b') = (HashSet.fromList a, HashSet.fromList b)
  in HashSet.toList $
    (a' `HashSet.difference` b') `HashSet.union` (b' `HashSet.difference` a')

-- Give the set of all type variables that are allocated in TVE but
-- not bound there
tvfree :: TVEnv -> TVBEnv -> [QTVarId]
tvfree venv benv = filter (not . flip IntMap.member benv) [0..fst venv-1]

-- `Shallow' substitution
-- Find a type that's not a variable, or is a free typevar
tvchase :: TVBEnv -> TVEnv -> K3 QType -> K3 QType
tvchase tvbe tve (tag -> QTVar v) | Just t <- tvblkup tvbe v = tvchase tvbe tve t
tvchase _ tve t = tvAddUIDSpan tve t

-- 'Shallow' substitution, additionally returning the last variable in
--  the chased chain.
tvchasev :: TVBEnv -> TVEnv -> K3 QType -> (Maybe QTVarId, K3 QType)
tvchasev tvbe tve t = loop Nothing t
  where
    loop _ (tag -> QTVar v) | Just ctv <- tvblkup tvbe v = loop (Just v) ctv
    loop lastV tv = (lastV, tvAddUIDSpan tve tv)

-- Compute (quite unoptimally) the characteristic function of the set
--  forall tvb \in fv(tve_before). Union fv(tvsub(tve_after,tvb))
--  i.e. For all free vars in before_env, we check if any of them has the given
--  var 'occur'ing in them in the after_env
tvDependentSet :: [QTVarId] -> TVBEnv -> QTVarId -> Bool
tvDependentSet tvFreeBefore tvbe_after tv =
    any (\tvb -> occurs tv (tvar tvb) tvbe_after) tvFreeBefore

-- Return the set of type variables in t. No duplicates
varsIn :: K3 QType -> IntSet
varsIn t = runIdentity $ foldMapTree extractVars IntSet.empty t
  where
    extractVars _ (tag -> QTVar v) = return $ IntSet.singleton v
    extractVars chAcc _ = return $ IntSet.unions chAcc

-- The occurs check: if v appears in t
-- First, get the last tvar v points to
-- Either any of the children of t have this tvar, or a QTVar in t links to this tvar
occurs :: QTVarId -> K3 QType -> TVBEnv -> Bool
occurs v t' tvbe = loop t'
  -- Follow v to the last tvar available
  where
    loop t@(tag -> QTOpen)    = any loop $ children t
    loop t@(tag -> QTConst _) = any loop $ children t
    loop (tag -> QTVar v2) | v == v2   = True
                           | otherwise = maybe False loop $ tvblkup tvbe v2
    loop _                  = False


{- TInfM helpers -}

runTInfM :: TIEnv -> TInfM a -> (Either String a, TIEnv)
runTInfM env m = flip runState env $ runEitherT m

reasonM :: (String -> String) -> TInfM a -> TInfM a
reasonM errf = mapEitherT $ \m -> do
  res <- m
  case res of
    Left err -> do
      env <- get
      return . Left . errf $ err ++ "\nType environment:\n" ++ pretty env
    Right _ -> return res

liftEitherM :: Either String a -> TInfM a
liftEitherM = either left return

getTVBE :: TInfM TVBEnv
getTVBE = liftM tvarBindEnv get

getTVE :: TInfM TVEnv
getTVE  = liftM tvarEnv get

-- Allocate a fresh type variable
newtv :: Maybe UID -> Maybe Span -> TInfM (K3 QType)
newtv muid mspan = do
  ienv <- get
  let (nv, ienv') = addVar ienv
  put ienv'
  return $ tvAddUIDSpan (tvarEnv ienv') $ tvar nv
  where
    addVar ienv =
      let env = tvarEnv ienv
          (nv, env') = tvinc env
          env'' = maybe env' (\uid -> tvext env' nv uid mspan) muid
      in (nv, ienv {tvarEnv=env''})

-- Deep substitute, throughout type structure
-- Chase down every type var's pointers, and substitute for the var
-- NOTE: deep substitution breaks links between types
--       Make sure not to break links for lowers or highers
--       We should not do it until the VERY end
tvsub ::  K3 QType -> TInfM (K3 QType)
tvsub = modifyTree sub
  where
    sub t@(tag -> QTVar id') = do
      tvbe <- getTVBE
      case tvblkup tvbe id' of
        Just t' -> tvsub t' >>= extendAnns t
        _       -> return t

    sub t = return t

    -- Add to tdest all the annotations of tsrc
    extendAnns tsrc' tdest = return $ foldl' (@+) tdest $
                              annotations tdest `difference` annotations tsrc'

-- | Replace one type with another throughout a tree
tvreplace :: IntMap QTVarId -> K3 QType -> K3 QType
tvreplace dict tree = runIdentity $ modifyTree sub tree
  where
    -- qtvars have no children
    sub t@(tag &&& annotations -> (QTVar id', annos)) =
      case IntMap.lookup id' dict of
        Just id'' -> return $ Node (QTVar id'' :@: annos) []
        _         -> return t
    sub t = return t

-- Unification helpers.
-- | Returns a self record and lifted attribute identifiers when given
--   a collection and a record that is a hacky supertype of said collection.
--   This is hacky because we only check that the records match the collection at the
--   id level. Collections are records because you can project on them.
collectionSubRecord :: K3 QType -> K3 QType -> TInfM (Maybe (K3 QType, [Identifier]))
collectionSubRecord ct@(getQTCollectionIds -> Just annIds)
                       (getQTRecordIdsCh   -> Just (ids, _))
  = liftM testF (get >>= mkColQT)
  where
    mkColQT tienv = do
      -- Get collection member environments for all annotations
      memEnvs <- mapM (liftEitherM . tilkupa tienv) annIds
      -- Make final and self types
      -- We don't care about the final type though
      mkCollectionFSQType annIds memEnvs $ head $ children ct

    -- Hack: check that the created record matches the record ids
    -- No deep check here
    testF (_, self)
      | QTConst (QTRecord liftedAttrIds) <- tag self
      , ids `subsetOf` liftedAttrIds
      = Just (self, liftedAttrIds)

    testF _ = Nothing

collectionSubRecord _ _ = return Nothing

-- Unify a free variable v1 with t2
unifyv :: QTVarId -> K3 QType -> TInfM ()
unifyv v1 t@(tag -> QTVar v2)
  | v1 == v2  = return ()

    -- Since they're both variables make one point to the other.
    -- TODO: chasev t before making v1 point to it
  | otherwise = trace (prettyTaggedSPair "unifyv var" v1 t) $
      modify $ modTvarBindEnv $ \tvbe -> tvbext tvbe v1 t

unifyv v t = do
  tvbe <- getTVBE
  tve  <- getTVE
  if occurs v t tvbe
    then do
      -- Recursive unification. Can only be for self
      -- Inject self into every record type in the type
      -- TODO: Check: is this ever activated?
      qt <- injectSelfQt tvbe tve t
      addToEnv "unifyv yes occurs" qt
    else
      -- just point the variable to the type
      addToEnv "unifyv no occurs" t

  where
    -- Replace all records that contain v with self
    injectSelfQt tvbe tve t' = mapTree (inject tvbe tve) t'

    -- Map goes up, so we need to handle both record and open record separately
    inject tvbe tve nch n@((tag &&& annotations) . tvchase tvbe tve -> (QTConst(QTRecord _), anns))
      | occurs v n tvbe = retTSelf anns
      | otherwise       = return $ Node (tag n :@: anns) nch

    -- We're at Open. Check the case where the child was a record
    inject _ _ [tag -> QTSelf, _] (Node (QTOpen :@: anns) [tag -> QTConst(QTRecord _), _])
      = retTSelf anns

    inject _ _ [_, tag -> QTSelf] (Node (QTOpen :@: anns) [_, tag -> QTConst(QTRecord _)])
      = retTSelf anns

    inject _ _ ch n = return $ Node (tag n :@: annotations n) ch

    retTSelf anns = return $ foldl' (@+) tself anns

    addToEnv str t' = trace (prettyTaggedSPair str v t') $
                       modify $ modTvarBindEnv $ \tvbe' -> tvbext tvbe' v t'

-- | Unification driver type synonyms.
type RecordParts = (K3 QType, QTData, [Identifier])
type QTypeCtor = [K3 QType] -> K3 QType
type UnifyPreF  a = K3 QType -> TInfM (a, K3 QType)
type UnifyPostF a = (a, a) -> K3 QType -> TInfM (K3 QType)

-- | A unification driver, i.e., common unification code for both
--   our standard unification method, and unification with variable overrides
--   For 2 lower bound types, we find the lowest
--   doOpen: whether we should get the widest type for open types or not
--           (we don't do it for lambda application)
unifyDrv :: (Show a) => UnifyPreF a -> UnifyPostF a -> Bool -> QTMutCheck -> K3 QType -> K3 QType -> TInfM (K3 QType)
unifyDrv preF postF allowSub mutCheck qt1 qt2 = do
    (p1, qt1') <- preF qt1
    (p2, qt2') <- preF qt2
    qt         <- trace (prettyTaggedPair "unifyDrv" qt1' qt2') $
                    unifyDrv' qt1' qt2'
    postF (p1, p2) qt

  where
    unifyDrv' :: K3 QType -> K3 QType -> TInfM (K3 QType)

    -- numeric type: deal with subtyping
    unifyDrv' t1@(isQTNumeric -> True) t2@(isQTNumeric -> True) =
      if checkSubtypes subtypeOf t1 t2 then
        combineSubtypes lower lower upper t1 t2
      else unifyErr t1 t2 "numeric-subtyping" ""
      where
        subtypeOf (QTPrimitive x) (QTPrimitive y) = qtEnumOfBase x <= qtEnumOfBase y
        subtypeOf x y = error $ "expected numbers but got ["++show x++"], ["++show y++"]"

        combineNumeric f l@(getQTNumeric -> Just x) r@(getQTNumeric -> Just y) =
          unifyAnno l r >>= return . foldl' (@+)
            (tprim $ qtBaseOfEnum $ f $ map qtEnumOfBase [x, y])

        combineNumeric _ x y = error $ "expected numeric but got ["++show x++"],["++show y++"]"

        lower = combineNumeric minimum
        upper = combineNumeric maximum

    -- other primitives don't subtype
    unifyDrv' t1@(tag -> QTPrimitive p1) (tag -> QTPrimitive p2)
      | p1 == p2  = return t1
      | otherwise = primitiveErr p1 p2

    -- | Self type unification
    --   TODO: Fix self type so we know which self is referred to
    unifyDrv' t1@(isQTCollection -> True) (tag -> QTSelf) = return t1
    unifyDrv' (tag -> QTSelf) t2@(isQTCollection -> True) = return t2

    -- | Record combinations with subtyping
    unifyDrv' t1@(isQTRecord -> True) t2@(isQTRecord -> True) =
      -- Check for correct subtyping
      if checkSubtypes subtypeOf t1 t2 then
        combineSubtypes lower lower upper t1 t2
      else unifyErr t1 t2 "record-subtyping" ""
      where
        -- subtype function for record-record
        subtypeOf (QTConst(QTRecord ids)) (QTConst(QTRecord ids')) = ids' `subsetOf` ids
        -- should never happen
        subtypeOf x y = error $ "expected records but got ["++show x++"], ["++show y++"]"

        -- Different ways to combine records, based on given function
        combineRecords f l r = do
          (common, diff) <- onOpenRecord l r
          liftM (foldl' (@+) $ trec $ f common diff) (unifyAnno l r)

        -- Combine common and different ids/children
        lower  = combineRecords (++)
        upper  = combineRecords const

    -- | Collection-as-record subtyping for projection
    --   Check that a record adequately unifies with a collection
    --   NOTE: Hacky. We don't really check for a unification. We only match on the ids
    unifyDrv' t1@(isQTCollection -> True) t2@(isQTRecord -> True)
      = collectionSubRecord t1 t2 >>= \x -> case x of
          Just (selfRecord, liftedAttrIds) -> onCollection selfRecord liftedAttrIds t1 t2
          _ -> unifyErr t1 t2 "collection-record" ""

    unifyDrv' t1@(isQTRecord -> True) t2@(isQTCollection -> True)
      = collectionSubRecord t2 t1 >>= \x -> case x of
          Just (selfRecord, liftedAttrIds) -> onCollection selfRecord liftedAttrIds t2 t1
          _ -> unifyErr t1 t2 "collection-record" ""

    -- | Collection subtyping
    unifyDrv' t1@(isQTCollection -> True) t2@(isQTCollection -> True) =
      -- Check for correct subtyping
      if checkSubtypes subtypeOf t1 t2 then
        combineSubtypes closed lower upper t1 t2
      else unifyErr t1 t2 "collection-subtyping" ""
      where
        -- subtype function for collection-collection
        subtypeOf (QTConst(QTCollection ids)) (QTConst(QTCollection ids')) = ids' `subsetOf` ids
        -- should never happen
        subtypeOf x y = error $ "expected collections but got ["++show x++"], ["++show y++"]"

        -- Different ways to combine collections, based on given function
        combineCollections f l@(tag -> QTConst(QTCollection ids))
                             r@(tag -> QTConst(QTCollection ids')) = do
          let newIds = f ids ids'
          ch' <- rcr (head $ children l) $ head $ children r
          liftM (foldl' (@+) $ tcol ch' newIds) $ unifyAnno l r
        combineCollections _ x y = error $ "expected collections but got ["++show x++"], ["++show y++"]"

        closed = combineCollections const
        lower  = combineCollections (\x y -> nub $ x ++ y)
        upper  = combineCollections intersection

    -- | Other constructors must match completely
    unifyDrv' t1@(tag -> QTConst d1) t2@(tag -> QTConst d2) =
      onChildren d1 d2 "datatypes" (children t1) (children t2) (tdata d1)

    unifyDrv' tv@(tag -> QTVar v) t = unifyv v t >> return tv
    unifyDrv' t tv@(tag -> QTVar v) = unifyv v t >> return tv

    -- | Top unifies with any value. Bottom unifies with only itself.
    unifyDrv' t1@(tag -> tg1) t2@(tag -> tg2)
      | tg1 == QTTop = return t2
      | tg2 == QTTop = return t1
      | tg1 == tg2   = return t1
      | otherwise    = unifyErr t1 t2 "qtypes" ""

    -- recurse unifyDrv
    -- We always recurse with full mutability check
    rcr :: K3 QType -> K3 QType -> TInfM (K3 QType)
    rcr a b = unifyDrv preF postF allowSub MutEq a b

    -- Join annotations together except for mutability contradiction
    unifyAnno :: K3 QType -> K3 QType -> TInfM [Annotation QType]
    unifyAnno sup@(annotations -> annA) sub@(annotations -> annB) =
      let annAB = nub $ annA ++ annB in
      case (sup @~ isQTQualified, sub @~ isQTQualified, mutCheck) of
        (Just x, Just y, _) | x == y               -> return annAB
        (Just QTImmutable, Just QTMutable, MutSub) -> return annAB
        (_, _, MutNone)                            -> return annAB
        _ -> unifyErr sup sub "mutability-annotations" ""

    -- Check if we meet subtyping criteria
    -- subF is the way we check one type is a subtype of the other
    checkSubtypes :: (QType -> QType -> Bool) -> K3 QType -> K3 QType -> Bool
    checkSubtypes subF super sub =
      if not allowSub then super == sub
      else case (super, sub) of
        -- Can't subtype match between open types
        (isQTOpen -> True, isQTOpen -> True) -> True
        -- Cases with regular types are always checked for subtyping constraints
        (getQTOpenTypes -> [tag -> l, tag -> l'], tag -> r) ->
            r `subMaybe` l  && l' `subMaybe` r
        (tag -> l, getQTOpenTypes -> [tag -> r, tag -> r']) ->
            r `subMaybe` l  && l `subMaybe` r'
        (tag -> l, tag -> r) -> r `subF` l
      where
        _        `subMaybe` QTBottom = True
        QTBottom `subMaybe` _        = True
        x        `subMaybe` y        = x `subF` y

    -- General function to combine subtypes
    -- closedF, lowerF, upperF: functions to combine closed types (or closed + lower/upper),
    -- lower types, and upper types, respectively
    combineSubtypes closedF lowerF upperF x' y' =
      case (x', y') of
        (getQTOpenTypes -> [l, l'],
         getQTOpenTypes -> [r, r']) -> do
        -- Cases with only open types: we extend both the lower and upper limits,
        -- if they exist
          v  <- doMaybe lowerF l r
          v' <- doMaybe upperF l' r'
          return $ topen v v'
        -- Cases with closed types: unify with both higher and lower
        -- Return whichever one isn't nothing
        (getQTOpenTypes -> [l,l'], r)  -> closedWithOpen r l l'
        (l, getQTOpenTypes -> [r,r'])  -> closedWithOpen l r r'
        (l, r)                         -> closedF l r
      where
        doMaybe :: (K3 QType -> K3 QType -> TInfM (K3 QType)) -> K3 QType -> K3 QType -> TInfM (K3 QType)
        doMaybe _ x (isQTBottom -> True) = return x
        doMaybe _ (isQTBottom -> True) y = return y
        doMaybe f x y                    = f x y

        -- Return a closed type
        closedWithOpen l r r' = do
          v' <- doMaybe closedF l r' -- unify with higher first
          v  <- doMaybe closedF l r
          -- If both unify, doesn't matter which one we return
          -- but we prefer the lower unification
          return $ if isQTBottom v' then v else v'

    -- Take a self type, list of attributes, collection type and record type, and
    -- unify the record with the collection
    onCollection :: K3 QType -> [Identifier] -> K3 QType -> K3 QType -> TInfM (K3 QType)
    onCollection selfQt liftedAttrIds
                 ct@(tag -> QTConst (QTCollection _)) (getQTRecordIdsCh -> Just (ids, ch))
      = do
          -- substitute col type into children of self record
          subChQt <- mapM (substituteSelfQt ct) $ children selfQt
          let selfPairs   = zip liftedAttrIds subChQt
              projSelfT   = projectNamedPairs ids selfPairs
              tdcon       = QTRecord liftedAttrIds
              errk        = "collection subtype"
              colCtor   _ = ct
          onChildren tdcon tdcon errk projSelfT ch colCtor

    onCollection _ _ ct rt =
      left $ unlines ["Invalid collection arguments:", pretty ct, "and", pretty rt]

    -- Return the common ids and different ids after unifying the common ids
    -- This function should only really have direct record ids
    onOpenRecord (getQTRecordIdsCh -> Just (ids, ch)) (getQTRecordIdsCh -> Just (ids', ch')) = do
      let allIdCh = zip (ids ++ ids') $ ch ++ ch'
          commonIds = ids `intersection` ids'
          diffIds = ids `diff2way` ids'
          commonlch = fromMaybe err $ shuffleNamedPairs commonIds $ zip ids  ch
          commonrch = fromMaybe err $ shuffleNamedPairs commonIds $ zip ids' ch'
          diffCh = fromMaybe err $ shuffleNamedPairs diffIds allIdCh
          err = error "Malfunction in shuffleNamedPairs"
      -- Recurse on the common children, unifying them
      commonCh <- zipWithM rcr commonlch commonrch
      return (zip commonIds commonCh, zip diffIds diffCh)

    onOpenRecord x y = error $ "OnOpenRecord: expected records but got ["++show x++"]["++show y++"]"

    -- TODO: widen the original varids

    -- If types are equal, recurse unify on their children
    onChildren :: QTData -> QTData -> String -> [K3 QType] -> [K3 QType] -> QTypeCtor -> TInfM (K3 QType)
    onChildren tga tgb kind a b ctor
      | tga == tgb = onList a b ctor $ \s -> unifyErr tga tgb kind s
      | otherwise  = unifyErr tga tgb kind ""

    -- Recurse unifyDrv over a list of types, constructing using ctor when done
    onList :: [K3 QType] -> [K3 QType] -> QTypeCtor -> (String -> TInfM (K3 QType)) -> TInfM (K3 QType)
    onList a b ctor errf =
      if length a == length b
        then liftM ctor $ zipWithM rcr a b
        else errf $ "Unification mismatch on lists:\nList 1:" ++ show a ++ "\nList 2:" ++ show b

    -- Substitute a collection type for self type inside a type
    substituteSelfQt :: K3 QType -> K3 QType -> TInfM (K3 QType)
    substituteSelfQt ct@(tag -> QTConst (QTCollection _)) qt = mapTree sub qt
      where sub _ (tag -> QTSelf) = return ct
            sub ch (Node n _)     = return $ Node n ch

    substituteSelfQt ct _ = subSelfErr ct

    -- Errors
    primitiveErr a b = unifyErr a b "primitives" ""

    unifyErr a b kind s =
      left $ unlines [
        "Unification mismatch on " ++ kind ++ " (" ++ s ++ "):",
        pretty a,
        pretty b
      ]

    subSelfErr ct = left $ boxToString $
      "Invalid self substitution, qtype is not a collection: " : prettyLines ct

tvAddUIDSpan :: TVEnv -> K3 QType -> K3 QType
tvAddUIDSpan tve n@(tag -> QTVar i) =
  case n @~ isQTUIDSpan of
    Just _  -> n
    Nothing ->
      let (muid, mspan) = tvlkup tve i
          n'  = maybe n  (\u -> n  @+ QTUID u) muid
          n'' = maybe n' (\s -> n' @+ QTSpan s) mspan
      in n''

tvAddUIDSpan _ n = n


-- | Type unification.
-- UnifyDrv with pre-tvchase
unifyM :: Bool -> K3 QType -> K3 QType -> (String -> String) -> TInfM ()
unifyM allowSub t1 t2 errf =
  trace (prettyTaggedPair "unifyM" t1 t2) $
    reasonM errf $ void $ unifyDrv preChase postId allowSub t1 t2
  where preChase qt = do
          tvbe <- getTVBE
          tve  <- getTVE
          return ((), tvchase tvbe tve qt)
        postId _    = return

-- Mutability modifier for unification
-- Only lasts one level deep, as any further is always a type error
data QTMutCheck = MutNone    -- We don't care about mutability
                | MutSub     -- We care and can subtype
                | MutEq      -- We care and mutability must be equal

-- | Type unification with variable overrides to the unification result.
-- TODO: is this necessary?
-- I think it makes the chain shorter
unifyWithOverrideM :: Bool -> QTMutCheck -> K3 QType -> K3 QType -> (String -> String) -> TInfM (K3 QType)
unifyWithOverrideM allowSub mutCheck qt1 qt2 errf = do
  trace (prettyTaggedPair "unifyOvM" qt1 qt2) $
    reasonM errf $ unifyDrv preChase postUnify allowSub mutCheck qt1 qt2
        -- as our first tuple member, return the last variable in the chain
  where preChase qt = do
          tvbe <- getTVBE
          tve  <- getTVE
          return $ tvchasev tvbe tve qt

        -- take the 'last variables' emitted by unifyDrv
        postUnify (v1, v2) qt = do
          tvbe <- getTVBE
          let vs = catMaybes [v1, v2]
          -- Check if occurs, if not, point last var at the unified type
          void $ mapM_ (\v -> unless (occurs v qt tvbe) $ unifyv v qt) vs
          return $ if null vs then qt
                   else foldl' (@+) (tvar $ head vs) $ annotations qt


-- | Given a polytype, for every polymorphic type var, replace all of
--   its occurrences in t with a fresh type variable.
instantiate :: QPType -> TInfM (K3 QType)
instantiate (QPType tvs t) = do
  let tvs' = IntSet.toList tvs
  vids <- mapM addFreshVar tvs'
  let vidMap = IntMap.fromList $ zip (map getId vids) tvs'
  return $ tvreplace vidMap t
  where
    getId (tag -> QTVar id') = id'
    getId x = error $ "expected QTVarId but got " ++ show x

    -- Add fresh varIds for all existing tvars
    addFreshVar tv = do
      -- Copy over old uid and span
      tve <- getTVE
      let (muid, mspan) = tvlkup tve tv
      newtv muid mspan

-- | Return a monomorphic polytype.
monomorphize :: (Monad m) => K3 QType -> m QPType
monomorphize t = return $ QPType IntSet.empty t

-- | Generalization for let-polymorphism.
generalize :: TInfM (K3 QType) -> TInfM QPType
generalize ta = do
  tvbe_before <- getTVBE
  tve_before  <- getTVE
  t           <- ta
  tvbe_after  <- getTVBE
  tve_after   <- getTVE
  -- Check for free vars that have been captured after the action
  -- We need fvs in t that are not bound in the environment
  -- This is potentially a very expensive action
  let freeBefore = tvfree tve_before tvbe_before
      tvdep = tvDependentSet freeBefore tvbe_after
      -- get the set of free vars
      freeAfter = IntSet.fromList $ tvfree tve_after tvbe_after
      fv  = IntSet.filter (\x -> x `IntSet.member` freeAfter && not (tvdep x)) $ varsIn t
  return $ QPType fv t

 -- ^ We return an unsubstituted type to preserve type variables
 --   for late binding based on overriding unification performed
 --   in function application.
 --   Old implementation: return $ QPType fv t'

-- | QType substitution helpers

-- | Replaces any type variables in a QType annotation on any subexpression.
substituteDeepQt :: K3 Expression -> TInfM (K3 Expression)
substituteDeepQt e = mapTree subNode e
  where subNode ch (Node (tg :@: anns) _) = do
          nanns <- mapM subAnns anns
          return (Node (tg :@: nanns) ch)

        subAnns (EQType qt) = liftM EQType $ tvsub qt
        subAnns x = return x

-- | Top-level type inference methods
inferProgramTypes :: K3 Declaration -> Either String (K3 Declaration)
inferProgramTypes prog = do
    -- Prepare the initial type environment
    (_, initEnv) <- let (a, b) = runTInfM tienv0 initializeTypeEnv
                    in liftM (, b) a
    fst $ runTInfM initEnv $ mapProgram declF annMemF exprF prog
  where
    initializeTypeEnv :: TInfM (K3 Declaration)
    initializeTypeEnv = mapProgram initDeclF initAMemF initExprF prog

    -- Make sure certain identifiers don't already exist in the environment
    withUnique' :: (TIEnv -> Identifier -> Either a b) -> String -> Identifier ->
                   TInfM (K3 Declaration) -> TInfM (K3 Declaration)
    withUnique' lookupF s n m =
                   failOnValid (return ()) (uniqueErr s n) (`lookupF` n) >>= const m

    withUnique  = withUnique' tilkupe "declaration"
    withUniqueA = withUnique' tilkupa "annotation"

    -- Fail on a successful application of a function
    failOnValid :: TInfM () -> TInfM () -> (TIEnv -> Either a b) -> TInfM ()
    failOnValid success failure f = do
      tienv <- get
      either (const success) (const failure) $ f tienv

    uniqueErr :: String -> Identifier -> TInfM a
    uniqueErr s n = left $ unwords ["Invalid unique", s, "identifier:", n]

    -- Create an initial declaration environment for recursive scope
    initDeclF :: K3 Declaration -> TInfM (K3 Declaration)
    initDeclF d@(tag &&& annotations -> (DGlobal n t _, annos))
      | isTFunction t = withUnique n $ do
          let muid  = annos @~ isDUID  >>= getUID
              mspan = annos @~ isDSpan >>= getSpan
          qpt <- qpType t muid mspan
          modify (\env -> tiexte env n qpt)
          return d
      | otherwise     = return d

    initDeclF d@(tag -> DTrigger n t _) =
      withUnique n $ do
        qpt <- trigType t
        modify (\env -> tiexte env n qpt)
        return d
      where
        trigType x = do
          qt <- qType x
          monomorphize $ ttrg qt

    initDeclF d@(tag &&& annotations -> (DAnnotation n tdeclvars mems, annos)) =
      withUniqueA n $ mkAnnMemEnv >> return d
      where muid  = annos @~ isDUID  >>= getUID
            mspan = annos @~ isDSpan >>= getSpan
            mkAnnMemEnv = do
              l <- mapM memType mems
              modify $ \env ->
                tiexta env n $ HashMap.fromList $ catMaybes l

            memType (Lifted      _ nm typ _ _) = unifyMemInit QPLifted   nm typ
            memType (Attribute   _ nm typ _ _) = unifyMemInit QPUnlifted nm typ
            memType (MAnnotation{})            = return Nothing

            unifyMemInit lifted nm typ = do
              qpt <- qpType (TC.forAll tdeclvars typ) muid mspan
              return $ Just (nm, (qpt, lifted))

    initDeclF d = return d

    initAMemF :: AnnMemDecl -> TInfM AnnMemDecl
    initAMemF = return

    initExprF :: K3 Expression -> TInfM (K3 Expression)
    initExprF = return

    unifyInitializer :: Identifier -> Either (Maybe QPType) QPType ->
                        Maybe (K3 Expression) -> TInfM (Maybe (K3 Expression))
    unifyInitializer n qptE eOpt = do
      qpt <- case qptE of
              -- Left is a global, Right is a trigger
              Left Nothing     -> get >>= \env -> liftEitherM (tilkupe env n)
              Left (Just qpt') -> modify (\env -> tiexte env n qpt') >> return qpt'
              Right qpt'       -> return qpt'

      case eOpt of
        Just e -> do
          qt1 <- instantiate qpt
          qt2 <- qTypeOfM e
          void $ unifyWithOverrideM True MutEqual qt1 qt2 $ mkErrorF e unifyInitErrF
          liftM Just $ substituteDeepQt e

        Nothing -> return Nothing

    -- Real type checking
    declF :: K3 Declaration -> TInfM (K3 Declaration)
    declF d@(tag &&& annotations -> (DGlobal n t eOpt, annos)) = do
      let muid  = annos @~ isDUID  >>= getUID
          mspan = annos @~ isDSpan >>= getSpan
      -- Left is a function, Right is a trigger
      qptE <- if isTFunction t then return $ Left Nothing
                               else liftM (Left . Just) $ qpType t muid mspan
      if isTEndpoint t then return d
        else do
          neOpt <- unifyInitializer n qptE eOpt
          return $ Node (DGlobal n t neOpt :@: annotations d) $ children d

    declF d@(tag -> DTrigger n t e) = do
      env <- get
      QPType qtvars qt <- liftEitherM (tilkupe env n)
      case tag qt of
        QTConst QTTrigger -> do
          -- Left is a function, Right is a trigger
          let nqptE = Right $ QPType qtvars $ tfun (head $ children qt) tunit
          neOpt <- unifyInitializer n nqptE (Just e)
          return $ maybe d (\ne -> Node (DTrigger n t ne :@: annotations d) $ children d) neOpt
        _ -> trigTypeErr n

    declF d@(tag -> DAnnotation n tvars mems) = do
        env   <- get
        tmEnv <- liftEitherM (tilkupa env n)
        nmems <- chkAnnMemEnv tmEnv
        return $ Node (DAnnotation n tvars nmems :@: annotations d) $ children d

      where chkAnnMemEnv :: TMEnv -> TInfM [AnnMemDecl]
            chkAnnMemEnv amEnv = mapM (memType amEnv) mems

            memType amEnv (Lifted mp mn mt meOpt mAnns) = do
              nmeOpt <- unifyMemInit amEnv mn meOpt
              return $ Lifted mp mn mt nmeOpt mAnns

            memType amEnv (Attribute mp mn mt meOpt mAnns) = do
              nmeOpt <- unifyMemInit amEnv mn meOpt
              return $ Attribute mp mn mt nmeOpt mAnns

            memType _ mem@(MAnnotation {}) = return mem

            unifyMemInit amEnv mn meOpt = do
              qpt <- maybe (memLookupErr mn) (return . fst) (HashMap.lookup mn amEnv)
              unifyInitializer mn (Right qpt) meOpt

    declF d = return d

    annMemF :: AnnMemDecl -> TInfM AnnMemDecl
    annMemF = return

    exprF :: K3 Expression -> TInfM (K3 Expression)
    exprF e = inferExprTypes e

    mkErrorF :: K3 Expression -> (String -> String) -> String -> String
    mkErrorF e f s = spanAsString ++ f s
      where spanAsString = let spans = mapMaybe getSpan $ annotations e
                           in if null spans
                                then boxToString $ ["["] %+ prettyLines e %+ ["]"]
                                else unwords ["[", show $ head spans, "] "]

    memLookupErr  n = left $ "No annotation member in initial environment: " ++ n
    trigTypeErr   n = left $ "Invlaid trigger declaration type for: " ++ n
    unifyInitErrF s = "Failed to unify initializer: " ++ s

-- | Expression type inference. Note this not perform a final type substitution,
--   leaving it to the caller as desired. This may leave type variables present
--   in the quicktype annotations attached to expressions.
inferExprTypes :: K3 Expression -> TInfM (K3 Expression)
inferExprTypes expr = mapIn1RebuildTree lambdaBinding sidewaysBinding inferQType expr

  where
    iu :: TInfM ()
    iu = return ()

    mkErrorF :: K3 Expression -> (String -> String) -> String -> String
    mkErrorF e f s = spanAsString ++ f s
      where spanAsString = let spans = mapMaybe getSpan $ annotations e
                           in if null spans then boxToString $ ["["] %+ prettyLines e %+ ["]"]
                                            else unwords ["[", show $ head spans, "] "]

    monoBinding :: Identifier -> K3 QType -> TInfM ()
    monoBinding i t = do
      mt <- monomorphize t
      modify (\env -> tiexte env i mt)

    lambdaBinding :: K3 Expression -> K3 Expression -> TInfM ()
    lambdaBinding _ n@(Node (ELambda i :@: _) _) = do
      let muid  = n @~ isEUID  >>= getUID
          mspan = n @~ isESpan >>= getSpan
      newtv muid mspan >>= monoBinding i

    lambdaBinding _ _ = return ()

    -- TODO: need to chase pointers in qTypeOfM
    sidewaysBinding :: K3 Expression -> K3 Expression -> TInfM [TInfM ()]

    sidewaysBinding ch1 (tag -> ELetIn i) = do
      ipt <- generalize $ qTypeOfM ch1
      modify $ \env -> tiexte env i ipt
      return [iu]

    sidewaysBinding ch1 n@(tag -> EBindAs b) = do
        ch1T <- qTypeOfM ch1
        let muid  = n @~ isEUID  >>= getUID
            mspan = n @~ isESpan >>= getSpan
        case b of
          BIndirection id' -> do
            itv <- newtv muid mspan
            void $ unifyWithOverrideM False MutSub ch1T (tind itv) $ bindErr "indirection"
            monoBinding id' itv

          BTuple ids -> do
            idtvs <- mapM (const $ newtv muid mspan) ids
            void $ unifyWithOverrideM False MutSub ch1T (ttup idtvs) $ bindErr "tuple"
            mapM_ (uncurry monoBinding) $ zip ids idtvs

          BRecord ids -> do
            tvs <- mapM (const $ newtv muid mspan) ids
            rtv <- newtv muid mspan
            let r = trec $ zip (map fst ids) tvs
            unifyv (getQTVarId rtv) (topen r tbot)
            void $ unifyWithOverrideM True MutSub ch1T r $ bindErr "record"
            mapM_ (uncurry monoBinding) $ zip (map snd ids) tvs

        return [iu]

      where
        bindErr kind reason = unwords ["Invalid", kind, "bind-as:", reason]

    sidewaysBinding ch1 n@(tag -> ECaseOf i) = do
      ch1T <- qTypeOfM ch1
      let muid  = n @~ isEUID  >>= getUID
          mspan = n @~ isESpan >>= getSpan
      itv  <- newtv muid mspan
      void $  unifyWithOverrideM False MutSub ch1T (topt itv) ("Invalid case-of source expression: "++)
      return [monoBinding i itv, modify $ \env -> tidele env i]

    sidewaysBinding _ (children -> ch) = return (replicate (length ch - 1) iu)

    inferQType :: [K3 Expression] -> K3 Expression -> TInfM (K3 Expression)
    inferQType _ n@(tag -> EConstant (CBool   _)) = return $ n .+ tbool
    inferQType _ n@(tag -> EConstant (CByte   _)) = return $ n .+ tbyte
    inferQType _ n@(tag -> EConstant (CInt    _)) = return $ n .+ tint
    inferQType _ n@(tag -> EConstant (CReal   _)) = return $ n .+ treal
    inferQType _ n@(tag -> EConstant (CString _)) = return $ n .+ tstr

    inferQType _ n@(tag -> EConstant (CNone nm)) = do
      let muid  = n @~ isEUID  >>= getUID
          mspan = n @~ isESpan >>= getSpan
      tv <- newtv muid mspan
      let ntv = case nm of
                  NoneMut   -> mutQT tv
                  NoneImmut -> immutQT tv
      return $ n .+ topt ntv

    inferQType _ n@(tag -> EConstant (CEmpty t)) = do
      cqt <- qType t
      let annIds =  namedEAnnotations $ annotations n
      colqt <- mkCollectionQType annIds cqt
      return $ n .+ colqt

    -- | Variable specialization.
    inferQType _ n@(tag -> EVariable id') = do
        env <- get
        qt  <- either (lookupError id') instantiate (tilkupe env id')
        return $ n .+ qt

    -- | Data structures. Qualifiers are taken from child expressions by rebuildE.
    -- TODO: actually they're not
    inferQType ch n@(tag -> ESome)       = qTypeOfM (head ch) >>=
                                             return . ((rebuildE n ch) .+) . topt
    inferQType ch n@(tag -> EIndirect)   = qTypeOfM (head ch) >>=
                                             return . ((rebuildE n ch) .+) . tind
    inferQType ch n@(tag -> ETuple)      = mapM qTypeOfM ch   >>=
                                             return . ((rebuildE n ch) .+) . ttup
    -- One of the few ways we can have a closed record
    inferQType ch n@(tag -> ERecord ids) =
      liftM ((rebuildE n ch .+) . trec . zip ids) $ mapM qTypeOfM ch


    -- | Lambda expressions already had tvars created in lambdabinding
    inferQType ch n@(tag -> ELambda i) = do
        env  <- get
        ipt  <- either (lambdaBindingErr i) return $ tilkupe env i
        chqt <- qTypeOfM $ head ch
        -- Delete the binding from the state now that we're going up the tree
        void $ modify $ \env' -> tidele env' i
        -- Check for monomorphism
        case ipt of
          QPType s iqt | s == IntSet.empty -> return $ rebuildE n ch .+ tfun iqt chqt
          _                                -> polyLambdaBindingErr

    -- | Assignment expressions unify their source and target types, as well as
    --   ensuring that the source is mutable.
    inferQType ch n@(tag -> EAssign id') = do
      env <- get
      ipt <- either (assignBindingErr id') return $ tilkupe env id'
      eqt <- qTypeOfM $ head ch
      case ipt of
        QPType s iqt -- monomorphic
          | s == IntSet.empty && iqt @~ isQTQualified == Just QTMutable -> do
              void $ unifyWithOverrideM False MutNone iqt eqt $
                mkErrorF n (("Invalid assignment to " ++ id' ++ ": ") ++)
              return $ rebuildE n ch .+ tunit
          | s == IntSet.empty -> mutabilityErr id'

        _ -> polyAssignBindingErr

    inferQType ch n@(tag -> EProject id') = do
      let muid  = n @~ isEUID  >>= getUID
          mspan = n @~ isESpan >>= getSpan
      srcqt   <- qTypeOfM $ head ch
      fieldqt <- newtv muid mspan
      rtv     <- newtv muid mspan
      let prjqt = topen (trec [(id', fieldqt)]) tbot
      unifyv (getQTVarId rtv) prjqt
      void $ trace (prettyTaggedPair ("infer prj " ++ id') srcqt prjqt)
           $ unifyWithOverrideM True MutNone srcqt rtv $ mkErrorF n
             (unlines ["Invalid record projection:", pretty srcqt, "and", pretty prjqt] ++)
      return $ rebuildE n ch .+ fieldqt

    -- TODO: add applied lower/higher to concretization set
    -- TODO: don't force lower unification on lambda application
    inferQType ch n@(tag -> EOperate OApp) = do
      let muid  = n @~ isEUID  >>= getUID
          mspan = n @~ isESpan >>= getSpan
      fnqt  <- qTypeOfM $ head ch
      argqt <- qTypeOfM $ last ch
      retqt <- newtv muid mspan
      let errf = mkErrorF n (unlines ["Invalid function application:",
                                       pretty fnqt,
                                       "and",
                                       pretty (tfun argqt retqt), ":"] ++)
      void $ trace (prettyTaggedTriple "infer app " n fnqt $ tfun argqt retqt) $
        -- TODO: Apply needs a special unification, since we don't want to widen records
        -- and we do want to preserve the subtype relation
        unifyWithOverrideM True MutSub fnqt (tfun argqt retqt) errf
      return $ rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EOperate OSeq) = do
        lqt <- qTypeOfM $ head ch
        rqt <- qTypeOfM $ last ch
        void $ unifyWithOverrideM False MutNone tunit lqt $ mkErrorF n ("Invalid left sequence operand: " ++)
        return $ rebuildE n ch .+ rqt

    -- | Check trigger-address pair and unify trigger type and message argument.
    inferQType ch n@(tag -> EOperate OSnd) = do
        let muid  = n @~ isEUID  >>= getUID
            mspan = n @~ isESpan >>= getSpan
        trgtv <- newtv muid mspan
        void $ unifyBinaryM MutSub (ttup [ttrg trgtv, taddr]) trgtv ch n sndError
        return $ rebuildE n ch .+ tunit

    -- | Unify operand types based on the kind of operator.
    inferQType ch n@(tag -> EOperate op)
      | numeric op = do
          -- create tvars so we can widen
          let muid  = n @~ isEUID  >>= getUID
              mspan = n @~ isESpan >>= getSpan
          tvl <- newtv muid mspan
          unifyv (getQTVarId tvl) $ topen tnum tbot
          tvr <- newtv muid mspan
          unifyv (getQTVarId tvr) $ topen tnum tbot
          (_, resultqt) <- unifyBinaryM MutNone tvl tvr ch n numericError
          return $ rebuildE n ch .+ resultqt

      | comparison op = do
          lqt <- qTypeOfM $ head ch
          rqt <- qTypeOfM $ last ch
          -- TODO: subtype for numeric only
          void $ unifyWithOverrideM True MutNone lqt rqt $ mkErrorF n comparisonError
          return $ rebuildE n ch .+ tbool

      | logic op = do
            void $ unifyBinaryM MutNone tbool tbool ch n logicError
            return $ rebuildE n ch .+ tbool

      | textual op = do
            void $ unifyBinaryM MutNone tstr tstr ch n stringError
            return $ rebuildE n ch .+ tstr

      | op == ONeg = do
            chqt <- unifyUnaryM MutNone (topen tnum tbot) ch $
                      mkErrorF n uminusError
            return $ rebuildE n ch .+ chqt

      | op == ONot = do
            void $ unifyUnaryM MutNone tbool ch $ mkErrorF n negateError
            return $ rebuildE n ch .+ tbool

      | otherwise = left $ "Invalid operation: " ++ show op

    -- First child generation has already been performed in sidewaysBinding
    -- Delete the identifier from the env as we leave this node
    inferQType ch n@(tag -> ELetIn j) = do
      bqt <- qTypeOfM $ last ch
      void $ modify $ \env -> tidele env j
      return $ rebuildE n ch .+ bqt

    -- First child unification has already been performed in sidewaysBinding
    -- Delete the identifiers from the env as we leave this node
    inferQType ch n@(tag -> EBindAs b) = do
      bqt <- qTypeOfM $ last ch
      case b of
        BIndirection i -> modify $ \env -> tidele env i
        BTuple ids     -> modify $ \env -> foldl' tidele env ids
        BRecord ids    -> modify $ \env -> foldl' tidele env $ map snd ids
      return $ rebuildE n ch .+ bqt

    -- First child unification has already been performed in sidewaysBinding
    inferQType ch n@(tag -> ECaseOf _) = do
      -- First child is EType, so skip it
      sqt   <- qTypeOfM $ ch !! 1
      nqt   <- qTypeOfM $ last ch
      retqt <- unifyWithOverrideM False MutEq sqt nqt $ mkErrorF n ("Mismatched case-of branch types: " ++)
      return $ rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EIfThenElse) = do
      pqt   <- qTypeOfM $ head ch
      tqt   <- qTypeOfM $ ch !! 1
      eqt   <- qTypeOfM $ last ch
      void $ unifyWithOverrideM False MutNone pqt tbool $
               mkErrorF n ("Invalid if-then-else predicate: " ++)
      retqt <- unifyWithOverrideM False MutEq tqt eqt $
                 mkErrorF n ("Mismatched condition branches: " ++)
      return $ rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EAddress) = do
      hostqt <- qTypeOfM $ head ch
      portqt <- qTypeOfM $ last ch
      void $ unifyWithOverrideM False MutNone hostqt tstr $
        mkErrorF n ("Invalid address host string: " ++)
      void $ unifyWithOverrideM False MutNone portqt tint $ mkErrorF n ("Invalid address port int: " ++)
      return $ rebuildE n ch .+ taddr

    inferQType ch n  = return $ rebuildE n ch
      -- ^ TODO unhandled: ESelf, EImperative
      -- ESelf should have annotations to compare to collections

    rebuildE (Node t _) ch = Node t ch

    unifyBinaryM mut lexpected rexpected ch n errf = do
      lqt <- qTypeOfM $ head ch
      rqt <- qTypeOfM $ last ch
      void $ unifyWithOverrideM True mut lexpected lqt (mkErrorF n $ errf "left")
      void $ unifyWithOverrideM True mut rexpected rqt (mkErrorF n $ errf "right")
      return (lqt, rqt)

    unifyUnaryM mut expected ch errf = do
        chqt <- qTypeOfM $ head ch
        void $ unifyWithOverrideM True mut chqt expected errf
        return chqt

    numeric    op = op `elem` [OAdd, OSub, OMul, ODiv, OMod]
    comparison op = op `elem` [OEqu, ONeq, OLth, OLeq, OGth, OGeq]
    logic      op = op `elem` [OAnd, OOr]
    textual    op = op `elem` [OConcat]

    lookupError j reason      = left $ unwords ["No type environment binding for ", j, ":", reason]
    lambdaBindingErr i reason = left $ unwords ["Could not find typevar for lambda binding: ", i, reason]
    polyLambdaBindingErr      = left "Invalid forall type in lambda binding"

    assignBindingErr i reason = left $ unwords ["Could not find binding type for assignment: ", i, reason]
    polyAssignBindingErr      = left "Invalid forall type in assignment"
    mutabilityErr j           = left $ "Invalid assigment to non-mutable binding: " ++ j

    sndError     side reason = "Invalid " ++ side ++ " send operand: " ++ reason
    numericError side reason = "Invalid " ++ side ++ " numeric operand: " ++ reason
    stringError  side reason = "Invalid " ++ side ++ " string operand: " ++ reason
    logicError   side reason = unwords ["Invalid", side, "logic", "operand:", reason]
    comparisonError   reason = "Invalid comparison operands:" ++ reason

    uminusError reason = "Invalid unary minus operand: " ++ reason
    negateError reason = "Invalid negation operand: " ++ reason


{- Collection type construction -}

-- Make a collection qtype based on the contents (always a record)
-- NOTE: limits collection content to a record
mkCollectionQType :: [Identifier] -> K3 QType -> TInfM (K3 QType)
mkCollectionQType annIds contentQt@(isQTRecord -> True) =
  return $ tcol contentQt annIds

mkCollectionQType _ qt = left $ "Invalid content record type: " ++ show qt


-- Make the final and self types of a collection
-- (with possibly many annotations)
-- Takes annotation names, annotation member environments, content qtype
-- Returns final and self types
-- final type has only regular members and content
-- self type has lifted members
mkCollectionFSQType :: [Identifier] -> [TMEnv] -> K3 QType ->
                       TInfM (K3 QType, K3 QType)
mkCollectionFSQType annIds memEnvs contentQt = do
    flatEnvs <- assertNoDuplicateIds
    -- boolean determines if it's lifted
    let (lifted, regular) = partition (isLifted . snd . snd) flatEnvs
    finalQt <- mkFinalQType contentQt $ removeLifted regular
    tempQt  <- instantiateMembers $ removeLifted lifted
    selfQt  <- subCTVars contentQt finalQt $ trec tempQt
    return (finalQt, selfQt)
  where
    removeLifted = map (second fst)

    -- Here we check that a collection can only have record content
    mkFinalQType :: K3 QType -> [(Identifier, QPType)] -> TInfM (K3 QType)
    mkFinalQType t@(tag -> QTConst (QTRecord ids)) regularMem = do
           regMems <- instantiateMembers regularMem
           return $ trec $ zip ids (children t) ++ regMems
    mkFinalQType t _ = nonRecordContentErr t

    -- Substitute for final and content types inside tree
    subCTVars content finalt tree = mapTree (subCF content finalt) tree
    subCF content _ _ (tag -> QTContent) = return content
    subCF _ finalt _  (tag -> QTFinal)   = return finalt
    subCF _ _ ch      (Node t _) = return $ Node t ch

    -- flatten all the member envs for a particular collection
    -- and find duplicate ids
    assertNoDuplicateIds =
      let flatEnvs = concatMap HashMap.toList memEnvs
          ids      = map fst flatEnvs
      in if nub ids /= ids then nameConflictErr else return flatEnvs

    -- Convert collection members (qptypes) into a list of id, qtype
    -- qptypes are polymorphic
    instantiateMembers :: [(Identifier, QPType)] -> TInfM [(Identifier, K3 QType)]
    instantiateMembers members = mapM doInst members
      where
        doInst (id', qpt) = do
          qpt' <- instantiate qpt
          return (id', qpt')

    nameConflictErr        =
      left $ "Conflicting annotation member names: " ++ show annIds
    nonRecordContentErr qt =
      left $ "Invalid content record type: " ++ show qt


{- Type conversion -}

qpType :: K3 Type -> Maybe UID -> Maybe Span -> TInfM QPType

-- | At top level foralls, we extend the declared var env in the type inference
--   environment with fresh qtype variables. This leads to substitutions for any
--   corresponding declared variables in the type tree.
qpType t@(tag -> TForall tvars) muid mspan = do
  -- Create varIds for all the forall variables
  tvmap <- mapM (idToNewVarId . (\(TypeVarDecl id' _ _) -> id')) tvars
  -- Add and then delete the temporary forall identifiers
  void $ modify $ extend tvmap
  chQt <- qType (head $ children t)
  void $ modify $ prune tvmap
  return $ QPType (IntSet.fromList $ map snd tvmap) chQt

  where
    idToNewVarId id' = do
      v   <- newtv muid mspan
      vId <- varId v
      return (id', vId)
    extend tvmap env = foldl' (\a (b,c) -> tiextdv a b c) env tvmap
    prune  tvmap env = foldl' (\a (b,_) -> tideldv a b) env tvmap
    varId (tag -> QTVar i) = return i
    varId _ = left "Invalid type variable for type var bindings"

qpType t _ _ = generalize (qType t)
  -- Old code: qType t >>= monomorphize

-- | We currently do not support forall type quantifiers present at an
--   arbitrary location in the K3 Type tree since forall types are not
--   part of the QType datatype and grammar.
--   The above qpType method constructs polymorphic QTypes, which handles
--   top-level polymorphic types, creating mappings for declared variables
--   in a K3 Type to QType typevars.
--
qType :: K3 Type -> TInfM (K3 QType)
qType t = liftM (mutabilityT t) $ foldMapTree mkQType (ttup []) t
-- TODO: handle lower and higher (function)
--       or not: we don't have an open record syntax?
  where
    mkQType _ (tag -> TTop)    = return ttop
    mkQType _ (tag -> TBottom) = return tbot

    mkQType _ (tag -> TBool)    = return tbool
    mkQType _ (tag -> TByte)    = return tbyte
    mkQType _ (tag -> TInt)     = return tint
    mkQType _ (tag -> TReal)    = return treal
    mkQType _ (tag -> TString)  = return tstr
    mkQType _ (tag -> TNumber)  = return tnum
    mkQType _ (tag -> TAddress) = return taddr

    mkQType ch n@(tag -> TOption)       = return $ topt $ mutability0 ch n
    mkQType ch n@(tag -> TIndirection)  = return $ tind $ mutability0 ch n
    mkQType ch n@(tag -> TTuple)        = return $ ttup $ mutabilityN ch n
    mkQType ch n@(tag -> TRecord ids)   = return $ trec $ zip ids $ mutabilityN ch n

    mkQType ch n@(tag -> TCollection) = do
        let cqt = head ch
        let annIds = namedTAnnotations $ annotations n
        mkCollectionQType annIds cqt

    mkQType ch (tag -> TFunction) = return $ tfun (head ch) $ last ch
    mkQType ch (tag -> TTrigger)  = return $ ttrg $ head ch
    mkQType ch (tag -> TSource)   = return $ tsrc $ head ch
    mkQType ch (tag -> TSink)     = return $ tsnk $ head ch

    mkQType _ (tag -> TBuiltIn TContent)   = return tcontent
    mkQType _ (tag -> TBuiltIn TStructure) = return tfinal
    mkQType _ (tag -> TBuiltIn TSelf)      = return tself

    mkQType _ (tag -> TDeclaredVar x) = do
      tienv <- get
      liftEitherM (tilkupdv tienv x)

    mkQType _ (tag -> TForall _) = left "Invalid forall type for QType"
      -- ^ TODO: we can only handle top-level foralls, and not arbitrary
      --   foralls nested in type trees.

    mkQType _ t_ = left $ "No QType construction for " ++ show t_

    mutability0 nch n = mutabilityT (head $ children n) $ head nch
    mutabilityN nch n = zipWith mutabilityT (children n) nch


-- | Converts all QType annotations on program expressions to K3 types.
translateProgramTypes :: K3 Declaration -> Either String (K3 Declaration)
translateProgramTypes prog = mapProgram declF annMemF exprF prog
  where declF   = return
        annMemF = return
        exprF   = translateExprTypes

translateExprTypes :: K3 Expression -> Either String (K3 Expression)
translateExprTypes expr = mapTree translate expr >>= \e -> return $ flip addTQualifier e $ exprTQualifier expr
  where
    translate nch e@(Node (tg :@: anns) _) = do
      let nch' = case tg of
                   ELetIn _ -> addTQualifier (letTQualifier e) (head nch) : tail nch
                   _        -> nch
      nanns <- mapM translateEQType $ filter (not . isEType) anns
      return (Node (tg :@: nanns) nch')

    addTQualifier tqOpt e@(Node (tg :@: anns) ch) =
      maybe e (\tq -> Node (tg :@: map (inject tq) anns) ch) tqOpt
      where inject tq (EType t) = maybe (EType $ t @+ tq) (const $ EType t) $ find isTQualified $ annotations t
            inject _ a = a

    letTQualifier  e = exprTQualifier $ head $ children e
    exprTQualifier e = maybe Nothing (Just . translateAnnotation) $ extractEQTypeQualifier e

    extractEQTypeQualifier e =
      case find isEQType $ annotations e of
        Just (EQType qt) -> find isQTQualified $ annotations qt
        _ -> Nothing

    translateEQType (EQType qt) = liftM EType $ translateQType qt
    translateEQType x = return x

    translateAnnotation a = case a of
      QTMutable   -> TMutable
      QTImmutable -> TImmutable
      x -> error $ "Expected mutability annotation but got " ++ show x


translateQType :: K3 QType -> Either String (K3 Type)
translateQType qt = mapTree translateWithMutability qt
  where translateWithMutability ch qt'@(tag -> QTConst tg)
          | tg `elem` [QTOption, QTIndirection, QTTuple] = translate (attachToChildren ch qt') qt'

        translateWithMutability ch qt'@(tag -> QTConst (QTRecord _)) = translate (attachToChildren ch qt') qt'

        translateWithMutability ch qt' = translate ch qt'

        attachToChildren ch qt' =
          zipWith (foldl' (@+)) ch $ map (map translateAnnotation . annotations) $ children qt'

        translateAnnotation a = case a of
          QTMutable   -> TMutable
          QTImmutable -> TImmutable
          x -> error $ "Expected mutability annotation but got " ++ show x

        translate _ qt'
          | QTBottom     <- tag qt' = return TC.bottom
          | QTTop        <- tag qt' = return TC.top
          | QTContent    <- tag qt' = return $ TC.builtIn TContent
          | QTFinal      <- tag qt' = return $ TC.builtIn TStructure
          | QTSelf       <- tag qt' = return $ TC.builtIn TSelf
          | QTVar v      <- tag qt' = return $ TC.declaredVar ("v" ++ show v)

        translate _ (tag -> QTPrimitive p) = case p of
          QTBool     -> return TC.bool
          QTByte     -> return TC.byte
          QTReal     -> return TC.real
          QTInt      -> return TC.int
          QTString   -> return TC.string
          QTAddress  -> return TC.address
          QTNumber   -> return TC.number

        translate ch (tag -> QTConst d) = case d of
          QTFunction          -> return $ TC.function (head ch) $ last ch
          QTOption            -> return $ TC.option $ head ch
          QTIndirection       -> return $ TC.indirection $ head ch
          QTTuple             -> return $ TC.tuple ch
          QTRecord        ids -> return $ TC.record $ zip ids ch
          QTCollection annIds -> return $ foldl' (@+) (TC.collection $ head ch) $ map TAnnotation annIds
          QTTrigger           -> return $ TC.trigger $ head ch
          QTSource            -> return $ TC.source $ head ch
          QTSink              -> return $ TC.sink $ head ch

        translate _ qt' = Left $ "No translation for: " ++ show qt'


{- Instances -}
instance Pretty TIEnv where
  prettyLines e =
    ["TEnv: "]   %$ indent 2 (prettyLines $ typeEnv e)  ++
    ["TAEnv: "]  %$ indent 2 (prettyLines $ annotEnv e) ++
    ["TDVEnv: "] %$ indent 2 (prettyLines $ declEnv e)  ++
    ["TVEnv: "]  %$ indent 2 (prettyLines $ tvarEnv e)  ++
    ["TBVEnv: "] %$ indent 2 (prettyLines $ tvarBindEnv e) ++
    ["TCEnv: "]  %$ indent 2 (prettyLines $ concEnv e)

instance Pretty [QPType] where
  prettyLines xs = [intercalate ", " $ map show xs]

instance (Show a, Pretty b) => Pretty (HashMap a b) where
  prettyLines = HashMap.foldlWithKey' (\acc k v -> acc ++ prettyPair (k,v)) []

instance (Pretty (QPType, QPLifted)) where
  prettyLines (t, l) = [show l ++ ": " ++ show t]

instance Pretty a => Pretty (IntMap a) where
  prettyLines = IntMap.foldlWithKey' (\acc k v -> acc ++ prettyPair (k,v)) []

instance Pretty IntSet where
  prettyLines x = [intercalate ", " $ map show $ IntSet.toList x]

instance Pretty TVEnv where
  prettyLines (n, m) = ("# vars: " ++ show n) : prettyLines m

instance Pretty (UID, Maybe Span) where
  prettyLines (u, ms) = [show u ++ maybe "" (\x -> ", " ++ show x) ms]

prettyPairList :: (Show a, Pretty b) => [(a,b)] -> [String]
prettyPairList l = foldl' (\acc kvPair -> acc ++ prettyPair kvPair) [] l

prettyPair :: (Show a, Pretty b) => (a,b) -> [String]
prettyPair (a,b) = [show a ++ " => "] %+ prettyLines b

prettyTaggedSPair :: (Show a, Pretty b) => String -> a -> b -> String
prettyTaggedSPair s a b = boxToString $ [s ++ " " ++ show a] %+ [" and "] %+ prettyLines b

prettyTaggedPair :: (Pretty a, Pretty b) => String -> a -> b -> String
prettyTaggedPair s a b = boxToString $ [s ++ " "] %+ prettyLines a %+ [" and "] %+ prettyLines b

prettyTaggedTriple :: (Pretty a, Pretty b, Pretty c) => String -> a -> b -> c -> String
prettyTaggedTriple s a b c = boxToString $ [s ++ " "] %+ prettyLines a %+ [" "] %+ prettyLines b %+ [" and "] %+ prettyLines c
