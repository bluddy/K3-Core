{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

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

-- TODO: add uids to type variables
-- TODO: deal with contravariance for functions passed in
-- TODO: basic problem: breaking the pointers. Need to keep them until the end
-- TODO: keep most varids one level deep (pointing to another id that has a type) to improve performance
-- NOTE: between lambda borders, we want to unify without forcing lowerbound expansion of types
--       and keep track of the connection for concretization

module Language.K3.Analysis.HMTypes.Inference where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Arrow (first, second)

import Data.Function
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.HashMap (HashMap)
import qualified Data.HashMap as HashMap
import Data.HashSet (HashSet)
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

-- Replace matching values in newIds newVs if there's an id match
rebuildNamedPairs :: [(Identifier, a)] -> [Identifier] -> [a] -> [a]
rebuildNamedPairs oldIdv newIds newVs = map (replaceNewPair $ zip newIds newVs) oldIdv
  where replaceNewPair pairs (k,v) = maybe v id $ lookup k pairs


-- | A type environment.
--   The first entry is the latest binding of the identifier
type TEnv = HashMap Identifier [(QPType, Maybe UID, Maybe Span)]

-- | Annotation member environment.
--   The boolean indicates whether the member is a lifted attribute.
type TMEnv = HashMap Identifier (QPType, Bool)

-- | Annotation type environment.
type TAEnv = HashMap Identifier TMEnv

-- | Declared type variable environment.
--   (Alwyas has a varId)
type TDVEnv = HashMap Identifier QTVarId

-- | A type variable allocation environment
--   1. the last assigned id
--   2. map of id to uid
type TVEnv = (QTVarId, (IntMap QTVarID (UID, Maybe Span)))

-- | A type variable binding environment.
--   1. map of id to type/other id
type TVBEnv = IntMap QTVarId (K3 QType)

-- | A concretization environment
--   Shows which types are applied to which other types, which must therefore
--   be their subtypes. Concretization will use this as a shortcut.
type TCEnv = (IntMap QTVarId (IntSet QTVarId))

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

tlkup :: TEnv -> Identifier -> Either String (QPType, Maybe UID, Maybe Span)
tlkup env x = maybe err (Right . head) $ HashMap.lookup x env
 where err = Left $ "Unbound variable in type environment: " ++ x

text :: TEnv -> Identifier -> QPType -> Maybe UID -> Maybe Span -> TEnv
text env k qt muid mspan =
  HashMap.insertWith (++) k [(t, muid, mspan)] env

tdel :: TEnv -> Identifier -> TEnv
tdel env x = HashMap.update removeFront x env
  where removeFront []     = Nothing
        removeFront (x:xs) = Just xs

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

tdvlkup :: TDVEnv -> Identifier -> Either String K3 QType
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

tclkup :: TCEnv -> QTVarId -> IntSet QTVarId
tclkup env id = IntMap.lookup id env

tclext :: TCEnv -> QTVarId -> QTVarId -> TCEnv
tclext env id id' = IntMap.insertWith (IntSet.unions) id (IntSet.singleton id') env

-- TVBEnv helpers
-- Type variable binding environment
tvbenv0 :: TVBEnv
tvbenv0 = IntMap.empty

tvblkup :: TVBEnv -> QTVarId -> Maybe (K3 QType)
tvblkup env v = IntMap.lookup v env

tvbext :: TVBEnv -> QTVarId -> K3 QType -> TVBEnv
tvbext env v t = (IntMap.insert v t env)


-- TVEnv helpers
-- Type Variable environment
tvenv0 :: TVEnv
tvenv0 = (0, IntMap.empty)

tvext :: TVEnv -> QTVarId -> UID -> Maybe Span -> TVEnv
tvext env v uid mspan = second (IntMap.insert v (uid, mspan)) env

tvinc :: TVEnv -> TVEnv
tvinc env = first ((+) 1) env

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
modTvarBindEnv f env = env { tvarBindEnv=f $ tvarEnv env}

modConcEnv :: (TCEnv -> TCEnv) -> TIEnv -> TIEnv
modConcEnv f env = env { concEnv = f $ concEnv env}

tilkupe :: TIEnv -> Identifier -> Either String (QPType, Maybe UID, Maybe Span)
tilkupe env x = tlkup (typeEnv env) x

tilkupa :: TIEnv -> Identifier -> Either String TMEnv
tilkupa env x = talkup (annotEnv env) x

tilkupdv :: TIEnv -> Identifier -> Either String (K3 QType)
tilkupdv env x = tdvlkup (declEnv env) x

tiexte :: TIEnv -> Identifier -> QPType -> Maybe UID -> Maybe Span -> TIEnv
tiexte env x t muid mspan = env { typeEnv=text (typeEnv env) x t muid mspan }

tiexta :: TIEnv -> Identifier -> TMEnv -> TIEnv
tiexta env x ate = env { annotEnv=taext (annotEnv env) x ate }

tiextdv :: TIEnv -> Identifier -> QTVarId -> TIEnv
tiextdv env x v = env { declEnv=tdvext (declEnv env) x v }

tidele :: TIEnv -> Identifier -> TIEnv
tidele env i = env {typeEnv=tdel (typeEnv te) i}

tideldv :: TIEnv -> Identifier -> TIEnv
tideldv env i = env {declEnv=tdvdel (declEnv env) i}

tiincrv :: TIEnv -> (QTVarId, TIEnv)
tiincrv env = env {tvarEnv = tvinc (tvarEnv env)}

-- General Utilities

-- Accurate subset calculation
subSetOf :: Eq a => [a] -> [a] -> Bool
subSetOf a b = HashSet.fromList a `Hashset.intersect` HashSet.fromList b == HashSet.fromList a

intersection :: [a] -> [a] -> [a]
intersection a b = HashSet.toList $ HashSet.fromList a `HashSet.intersect` HashSet.fromList b

difference :: [a] -> [a] -> [a]
difference a b = HashSet.toList $ HashSet.fromList a HashSet.\\ HashSet.fromList b

-- Give the set of all type variables that are allocated in TVE but
-- not bound there
tvfree :: TVEnv -> TVBEnv -> [QTVarId]
tvfree venv benv = filter (not . (flip IntMap.member benv)) [0..(fst venv)-1]

-- `Shallow' substitution
-- Find a type that's not a variable, or is a free typevar
tvchase :: TVBEnv -> K3 QType -> K3 QType
tvchase tbe (tag -> QTVar v) | Just t <- tvblkup tbe v = tvchase tbe t
tvchase _ t = t

-- 'Shallow' substitution, additionally returning the last variable in
--  the chased chain.
tvchasev :: TVBEnv -> Maybe QTVarId -> K3 QType -> (Maybe QTVarId, K3 QType)
tvchasev tbe _ (tag -> QTVar v) | Just ctv <- tvblkup tbe v = tvchasev tbe (Just v) ctv
tvchasev _ lastV tv = (lastV, tv)

-- NOTE: is this necessary? Is freevar not enough?
-- Compute (quite unoptimally) the characteristic function of the set
--  forall tvb \in fv(tve_before). Union fv(tvsub(tve_after,tvb))
--  i.e. For all free vars in before_env, we check if any of them has the given
--  var 'occur'ing in them in the after_env
tvDependentSet :: [QTVarId] -> TBVEnv -> (QTVarId -> Bool)
tvDependentSet tvFreeBefore tvbe_after =
    \tv -> any (\tvb -> occurs tv (tvar tvb) tvbe_after) tvFreeBefore

-- Return the set of type variables in t. No duplicates
varsIn :: K3 QType -> IntSet
varsIn t = IntSet.toList $ runIdentity $ foldMapTree extractVars Set.empty t
  where
    extractVars _ (tag -> QTVar v) = return $ Set.singleton v
    extractVars chAcc _ = return $ Set.unions chAcc

-- The occurs check: if v appears in t
-- First, get the last tvar v points to
-- Either any of the children of t have this tvar, or a QTVar in t links to this tvar
occurs :: QTVarId -> K3 QType -> TVBEnv -> Bool
occurs v t env =
  -- Follow v to the last tvar available
  let v' = maybe v id $ fst $ tvchasev env v
  in loop t
  where
    loop (QTConst _) = or $ map loop $ children t
    loop (QTVar v2)  | v' == v2  = True
                     | otherwise = maybe False loop $ tvblkup tvbe v2
    loop _           = False


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
    Right r -> return res

liftEitherM :: Either String a -> TInfM a
liftEitherM = either left return

getTVBE :: TInfM TVBEnv
getTVBE = get >>= return . tvarBindEnv

-- Allocate a fresh type variable
newtv :: Maybe UID -> Maybe Span -> TInfM (K3 QType)
newtv muid mspan = do
  env <- get
  let (nv, env') = tiincrv env
      env'' = maybe env' (tvext env' nv uid mspan) muid
  put env''
  return $ tvar nv

-- Deep substitute, throughout type structure
-- Chase down every type var's pointers, and substitute for the var
-- NOTE: deep substitution breaks links between types
--       Make sure not to break links for lowers or highers
--       We should not do it until the VERY end

tvsub :: K3 QType -> TInfM (K3 QType)
tvsub qt = mapTree sub qt
  where
    sub ch t@(tag -> QTConst d) = return $ foldl (@+) (tdata d ch) $ annotations t

    sub _ t@(tag -> QTVar v) = do
      tvbe <- getTVBE
      case tvblkup tvbe v of
        Just t' -> tvsub t' >>= extendAnns t
        _       -> return t

    sub _ t = return t

    -- Add to tdest all the annotations of tsrc
    extendAnns tsrc tdest = return $ foldl (@+) tdest $
                              annotations tdest `difference` annotations tsrc

-- | Lower bound computation for numeric and record types.
--   Called by unify on nums and records
--   This function does not preserve annotations.(NOTE: why?)
--   Really, this is just an expansion to the widest (lowest) type possible, with no
--   connection to super or subtype
tvlower :: K3 QType -> K3 QType -> TInfM (K3 QType)
tvlower t1 t2 = getTVBE >>= \tvbe -> loop t1 t2
  where
    loop a b = tvlower' (tvchase tvbe a) (tvchase tvbe b)

    tvlower' x@(tag -> QTPrimitive p1) y@(tag -> QTPrimitive p2)
      | [p1, p2] `subsetOf` [QTReal, QTInt, QTNumber] ->
        -- Union of all annotations but mutability
        annLower x y >>=
        -- Find lowest common primitive type, and add combined annotations
          return . foldl (@+) (tprim $ qtBaseOfEnum $ minimum $ map qtEnumOfBase [p1,p2])
      | p1 == p2 -> return x

    -- Open record types on both sides: widen to widest type
    tvlower' x@(QTLower(QTConst (QTRecord ids))) y@(QTLower(QTConst (QTRecord ids'))) =
        mergedRecord True ids x ids' y

    -- Open record and closed record. Widen to closed record if it matches
    tvlower' x@((QTConst (QTRecord ids)) y@(QTLower(QTConst (QTRecord ids')))
      | ids' `subsetOf` ids  = mergedRecord False ids x ids' y
    tvlower' x@((QTLower(QTConst (QTRecord ids))) y@(QTConst (QTRecord ids'))
      | ids  `subsetOf` ids' = mergedRecord False ids x ids' y


     -- TODO: collections: do we need open/closed collection types?
      (QTCon (QTCollection _), QTCon (QTRecord _)) -> coveringCollection a' b'
      (QTCon (QTRecord _), QTCon (QTCollection _)) -> coveringCollection b' a'

      (QTCon (QTCollection idsA), QTCon (QTCollection idsB))
        | idsA `subsetOf` idsB -> mergedCollection idsB a' b'
        | idsB `subsetOf` idsA -> mergedCollection idsA a' b'

    -- Free variables. Will be connected by unification
    tvlower' x@(QTVar _) (QTVar _) = return x
    -- TODO: check the next 2 carefully
    tvlower' x@(QTVar _) _  = return x
    tvlower' _ y@(QTVar _)  = return y

      -- Closed record types: only if they match 100%
      -- We iterate over their children
    tvlower' x@(QTConst (QTRecord ids)) y@QTConst (QTRecord ids')) | x == y = do
      let (idts, idts') = (zip ids $ children x, zip ids' $ children y)
      ch <- mapM (\(k,v) -> loop v $ lookup k idts') idts
      annlower qt1 qt2 >>=
        return . foldl (@+) (tdata d ch)

    -- handle tuples and other constructors: if they match, we iterate over their children
    tvlower' x@(QTConst d) y@(QTConst _) | x == y = do
      ch <- mapM (uncurry loop) $ zip (children x) (children y)
      annlower x y >>=
        return . foldl (@+) (tdata d ch)

    -- other primitives are ok if they match
    tvlower' x y | x == y = x

    -- no match on both sides means a mismatch
    tvlower' x y = lowerError x y

    mergedRecord lower ids1 qt1 ids2 qt2 = do
      let commonIds = ids1 `intersect` ids2
          diffIds   = ids1 ++ ids2 `difference` inter
          idts1     = zip ids1 $ children qt1
          idts2     = zip ids2 $ children qt2
          extras    = map (flip lookup idts1) diffIds ++ map (flip lookup idts2) diffIds
          makeRec   = if lower then tlowerrec else trec

      fieldQt <- mapM (\k -> loop (lookup k idts1) (lookup k idts2)) commonIds
      annLower qt1 qt2 >>=
        return . foldl (@+) (makeRec $ zip commonIds fieldQt ++ zip diffIds extras)

    mergedCollection annIds ct1 ct2 = do
       -- run tvlower on the record of the element type
       ctntLower <- tvlower (head $ children ct1) (head $ children ct2)
       annLower ct1 ct2 >>=
         return . foldl (@+) (tcol ctntLower annIds)

    -- Merge collection and record that fits it
    -- NOTE: this shouldn't be necessary. We can type as if collections
    -- can contain anything, and then just remove the ones that don't have
    -- records
    coveringCollection ct rt@(tag -> QTCon (QTRecord _)) =
      collectionSubRecord ct rt >>= \case
        Just _ -> return ct
        _      -> lowerError ct rt

    coveringCollection x y = lowerError x y

    -- Join annotations together for lower, except for mutability contradiction
    annLower x@(annotations -> annA) y@(annotations -> annB) =
      let annAB   = nub $ annA ++ annB
          invalid = [QTMutable, QTImmutable]
      in if invalid `subsetOf` annAB then lowerError x y else return annAB

-- | Type operator evaluation.
-- Run tvlower on list of types, getting the lower bound at each step
tvopeval :: QTOp -> [K3 QType] -> TInfM (K3 QType)
tvopeval _ [] = left $ "Invalid qt operator arguments"
tvopeval QTLower ch = foldM tvlower (head ch) $ tail ch

-- Split into direct types and typevars
-- Run lower on direct types, then unify and lower type variables with them
-- If we have only direct types, run lower on them
-- If we have only typevars, unify amongst them first
consistentTLower :: [K3 QType] -> TInfM (K3 QType)
consistentTLower ch =
    case partition isQTVar $ nub ch of
      ([], [])          -> left "Invalid lower qtype"
      ([], nonvarCh)    -> return $ tlower $ nonvarCh
      (varCh, [])       -> do
        tve <- getTVE
        unifiedLower (tail varCh) (tvchase tve $ head varCh)
      (varCh, nonVarCh) -> tvopeval QTLower nonvarCh >>= unifiedLower varCh
  where
    -- Run lower on type variables, after unifying with a real type
    unifiedLower vch lb = do
      void $ mapM_ (extractAndUnifyV lb) vch
      return $ tlower $ [lb]++vch

    extractAndUnifyV t (tag -> QTVar v) = unifyv v t
    extractAndUnifyV _ _ = left "Invalid type var during lower qtype merge"

-- Unification helpers.
-- | Returns a self record and lifted attribute identifiers when given
--   a collection and a record that is a subtype of the collection.
--   Collections are also records because you can project on them (lifted attributes)
collectionSubRecord :: K3 QType -> K3 QType -> TInfM (Maybe (K3 QType, [Identifier]))
collectionSubRecord ct@(tag -> QTConst (QTCollection annIds))
                       (tag -> QTConst (QTRecord ids))
  = get >>= mkColQT >>= return . testF
  where
    mkColQT tienv = do
      -- Get collection member environments for all annotations
      memEnvs <- mapM (liftEitherM . tilkupa tienv) annIds
      -- Make final and self types
      mkCollectionFSQType annIds memEnvs (last $ children ct)

    -- Check that the created record matches the record ids
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
      modify $ modTvarEnv $ \tve -> tvext tve v1 t

unifyv v t = do
  tvbe <- getTVBE
  if not $ occurs v t tvbe then
    -- just point the variable to the type
    trace (prettyTaggedSPair "unifyv noc" v t) $
      modify $ modTvarBindEnv $ \tvbe' -> tvbext tvbe' v t
  else do
    -- Recursive unification. Can only be for self
    -- Inject self into every record type in the type
    -- Why isn't a collection handled here? Do we just assume that recursion
    -- can only work in collection self types?
    qt' <- injectSelfQt tve t
    trace (prettyTaggedSPair "unifyv yoc" v qt') $
      modify $ modTvarEnv $ \tvbe' -> tvbext tvbe' v qt'

  where
    injectSelfQt tvbe qt = mapTree (inject tvbe) qt

    inject tvbe nch n@(tvchase tvbe -> Node (QTLower (QTCon (QTRecord _)) :@: anns) _)
      | occurs v n tbve = return $ foldl (@+) tself anns
      | otherwise = return $ Node (tag n :@: anns) nch

    inject _ ch n = return $ Node (tag n :@: annotations n) ch

-- | Unification driver type synonyms.
type RecordParts = (K3 QType, QTData, [Identifier])
type QTypeCtor = [K3 QType] -> K3 QType
type UnifyPreF  a = K3 QType -> TInfM (a, K3 QType)
type UnifyPostF a = (a, a) -> K3 QType -> TInfM (K3 QType)

-- | A unification driver, i.e., common unification code for both
--   our standard unification method, and unification with variable overrides
unifyDrv :: (Show a) => UnifyPreF a -> UnifyPostF a -> K3 QType -> K3 QType -> TInfM (K3 QType)
unifyDrv preF postF qt1 qt2 = do
    (p1, qt1') <- preF qt1
    (p2, qt2') <- preF qt2
    qt         <- trace (prettyTaggedPair "unifyDrv" qt1' qt2') $
                    unifyDrv' qt1' qt2'
    postF (p1, p2) qt

  where
    unifyDrv' :: K3 QType -> K3 QType -> TInfM (K3 QType)

    -- numeric type: get lower bound
    unifyDrv' t1@(isQTNumeric -> True) t2@(isQTNumeric -> True) = tvlower t1 t2

    -- other primitives have to match
    unifyDrv' t1@(tag -> QTPrimitive p1) (tag -> QTPrimitive p2)
      | p1 == p2  = return t1
      | otherwise = primitiveErr p1 p2 (annotations t1 ++ annotations t2)

    -- | Self type unification
    --   We don't know which collection self refers to
    unifyDrv' t1@(tag -> QTCon (QTCollection _)) (tag -> QTSelf) = return t1
    unifyDrv' (tag -> QTSelf) t2@(tag -> QTCon (QTCollection _)) = return t2

    -- | Record subtyping for projection
    -- TODO: this doesn't consider open vs. closed records cleanly/correctly
    unifyDrv' t1@(tag -> QTConst d1@(QTRecord f1))
              t2@(tag -> QTConst d2@(QTRecord f2))
      | f1 `subsetOf` f2 = onRecord (t1,d1,f1) (t2,d2,f2)
      | f2 `subsetOf` f1 = onRecord (t2,d2,f2) (t1,d1,f1)

    -- | Collection-as-record subtyping for projection
    --   Check that a record adequately unifies with a collection
    unifyDrv' t1@(tag -> QTConst (QTCollection _)) t2@(tag -> QTConst (QTRecord _))
      = collectionSubRecord t1 t2 >>= \case
          Just (selfRecord, liftedAttrIds) -> onCollection selfRecord liftedAttrIds t1 t2
          _ -> unifyErr t1 t2 "collection-record" ""

    unifyDrv' t1@(tag -> QTConst (QTRecord _)) t2@(tag -> QTConst (QTCollection _))
      = collectionSubRecord t2 t1 >>= \case
          Just (selfRecord, liftedAttrIds) -> onCollection selfRecord liftedAttrIds t2 t1
          _ -> unifyErr t1 t2 "collection-record" ""

    unifyDrv' t1@(tag -> QTConst (QTCollection idsA)) t2@(tag -> QTConst (QTCollection idsB))
        | idsA `subsetOf` idsB = onCollectionPair idsB t1 t2
        | idsB `subsetOf` idsA = onCollectionPair idsA t1 t2
        | otherwise            = unifyErr t1 t2 "collection-collection"

    unifyDrv' t1@(tag -> QTConst d1) t2@(tag -> QTConst d2) =
      onChildren d1 d2 "datatypes" (children t1) (children t2) (tdata d1)

    -- | Unification of a delayed LB operator applies to the lower bounds of each set.
    --   This returns a merged delayed LB operator containing all variables, and the lower
    --   bound of the non-variable elements.
    --   TODO: almost all records should be lower bound/higher bound
    --   NOTE: not sure this is what we want to do
    unifyDrv' t1@(tag -> QTOperator QTLower) t2@(tag -> QTOperator QTLower) = do
      lb1 <- lowerBound t1 -- get lower bound of all things below t1
      lb2 <- lowerBound t2 -- "" t2
      lbs <- case (tag lb1, tag lb2) of
               (QTCon (QTRecord _), QTCon (QTRecord _)) -> do
                 lb' <- tvlower lb1 lb2
                 return $ if lb' `elem` [lb1, lb2] then [lb1,lb2] else [lb',lb1,lb2]
               (_,_) -> return [lb1, lb2]
      -- We unify all the lower bounds. Does this make sense?
      void $ foldM rcr (head $ lbs) $ tail lbs
      -- To return a type, we do this again... hmm
      consistentTLower $ children t1 ++ children t2

    -- TODO: we should check that tv is free. Otherwise we can cause a loop, no?
    -- I guess that's covered by the occurs check
    unifyDrv' tv@(tag -> QTVar v) t = unifyv v t >> return tv
    unifyDrv' t tv@(tag -> QTVar v) = unifyv v t >> return tv

    -- | Unification of a lower bound with a non-bound applies to the non-bound
    --   and the lower bound of the deferred set.
    --   This pattern match applies after type variable unification to allow typevars
    --   to match the lower-bound set.
    unifyDrv' t1@(tag -> QTOperator QTLower) t2 = do
      lb1 <- lowerBound t1
      void $ rcr lb1 t2
      r <- consistentTLower $ children t1 ++ [t2]
      trace (boxToString $ ["consistentTLowerL "] %+ prettyLines r) $ return r

    unifyDrv' t1 t2@(tag -> QTOperator QTLower) = do
      lb2 <- lowerBound t2
      void $ rcr t1 lb2
      r <- consistentTLower $ [t1] ++ children t2
      trace (boxToString $ ["consistentTLowerR "] %+ prettyLines r) $ return r

    -- | Top unifies with any value. Bottom unifies with only itself.
    unifyDrv' t1@(tag -> tg1) t2@(tag -> tg2)
      | tg1 == QTTop = return t2
      | tg2 == QTTop = return t1
      | tg1 == tg2   = return t1
      | otherwise    = unifyErr t1 t2 "qtypes" ""

    -- recurse unifyDrv
    rcr :: K3 QType -> K3 QType -> TInfM (K3 QType)
    rcr a b = unifyDrv preF postF a b

    -- recurse on the pair of content of each collection
    -- Annotations are taken care of by caller
    onCollectionPair :: [Identifier] -> K3 QType -> K3 QType -> TInfM (K3 QType)
    onCollectionPair annIds t1 t2 = rcr (head $ children t1) (head $ children t2) >>=
                                      return . flip tcol annIds

    -- Take a self type, list of attributes, collection type and record type, and
    -- unify the record with the collection
    onCollection :: K3 QType -> [Identifier] -> K3 QType -> K3 QType -> TInfM (K3 QType)
    onCollection selfQt liftedAttrIds
                 ct@(tag -> QTCon (QTCollection _)) rt@(tag -> QTCon (QTRecord ids))
      = do
          -- substitute col type into children of self record
          subChQt <- mapM (substituteSelfQt ct) $ children selfQt
          let selfPairs   = zip liftedAttrIds subChQt
              projSelfT   = projectNamedPairs ids selfPairs
              tdcon       = QTRecord liftedAttrIds
              errk        = "collection subtype"
              colCtor   _ = ct
          onChildren tdcon tdcon errk projSelfT (children rt) colCtor

    onCollection _ _ ct rt =
      left $ unlines ["Invalid collection arguments:", pretty ct, "and", pretty rt]

    -- unify records, where one is a supertype and another is a subtype
    onRecord :: RecordParts -> RecordParts -> TInfM (K3 QType)
    onRecord (supT, supCon, supIds) (subT, subCon, subIds) =
      let subPairs    = zip subIds $ children subT
          -- get the subtypes corresponding to labels that are also in the supertype
          subProjT    = projectNamedPairs supIds $ subPairs
          errkind     = "record subtype"
          -- Final constructor once we find the unification:
          -- We can only unify the supertype labels, so keep those unified values and add
          -- the subtype labels
          recCtor nch = tdata subCon $ rebuildNamedPairs subPairs supIds nch
      in onChildren supCon supCon errkind (children supT) subProjT recCtor

    -- If types are equal, recurse unify on their children
    onChildren :: QTData -> QTData -> String -> [K3 QType] -> [K3 QType] -> QTypeCtor -> TInfM (K3 QType)
    onChildren tga tgb kind a b ctor
      | tga == tgb = onList a b ctor $ \s -> unifyErr tga tgb kind s
      | otherwise  = unifyErr tga tgb kind ""

    -- Recurse unifyDrv over a list of types, constructing using ctor when done
    onList :: [K3 QType] -> [K3 QType] -> QTypeCtor -> (String -> TInfM (K3 QType)) -> TInfM (K3 QType)
    onList a b ctor errf =
      if length a == length b
        then mapM (uncurry rcr) (zip a b) >>= return . ctor
        else errf "Unification mismatch on lists."

    -- Substitute a collection type for self type inside a type
    substituteSelfQt :: K3 QType -> K3 QType -> TInfM (K3 QType)
    substituteSelfQt ct@(tag -> QTCon (QTCollection _)) qt = mapTree sub qt
      where sub _ (tag -> QTSelf) = return $ ct
            sub ch (Node n _)     = return $ Node n ch

    substituteSelfQt ct _ = subSelfErr ct

    lowerBound t = tvopeval QTLower $ children t

    -- Errors
    primitiveErr a b annos = unifyErr a b "primitives" "" annos

    unifyErr a b kind s annos =
      let uidAnnos = filter isQTUID annos in
      left $ unlines [
        unwords ["Unification mismatch on ", kind, "(", s, "):"],
        pretty a,
        pretty b,
        unwords $ "At uids: ":intersperse ", " $ map (show . getQTUID) annos
      ]


    subSelfErr ct = left $ boxToString $ ["Invalid self substitution, qtype is not a collection: "] ++ prettyLines ct

-- | Type unification.
-- UnifyDrv with pre-tvchase
unifyM :: K3 QType -> K3 QType -> (String -> String) -> TInfM ()
unifyM t1 t2 errf = trace (prettyTaggedPair "unifyM" t1 t2) $
                      reasonM errf $ void $ unifyDrv preChase postId t1 t2
  where preChase qt = getTVE >>= \tve -> return ((), tvchase tve qt)
        postId _ qt = return qt

-- | Type unification with variable overrides to the unification result.
-- TODO: is this necessary?
-- I think it makes the chain shorter
unifyWithOverrideM :: K3 QType -> K3 QType -> (String -> String) -> TInfM (K3 QType)
unifyWithOverrideM qt1 qt2 errf = trace (prettyTaggedPair "unifyOvM" qt1 qt2) $
                                    reasonM errf $ unifyDrv preChase postUnify qt1 qt2
        -- as our first tuple member, return the last variable in the chain
  where preChase qt = getTVE >>= \tve -> return $ tvchasev tve Nothing qt
        -- take the 'last variables' emitted by unifyDrv
        postUnify (v1, v2) qt = do
          tve <- getTVE
          let vs = catMaybes [v1, v2]
          -- Check if occurs, if so, unify var again
          void $ mapM_ (\v -> if occurs v qt tve then return ()
                              else unifyv v qt) vs
          return $ if null vs then qt
                   else (foldl (@+) (tvar $ head vs) $ annotations qt)


-- | Given a polytype, for every polymorphic type var, replace all of
--   its occurrences in t with a fresh type variable. We do this by
--   creating a substitution tve and applying it to t.
--   The new types will unify with our application site.
--   We also strip any mutability qualifiers here since we only instantiate
--   on variable access. (NOTE: is this true?)
instantiate :: QPType -> TInfM (K3 QType)
instantiate (QPType tvs t) = withFreshTVE $ do
  Node (tg :@: anns) ch <- tvsub t
  return $ Node (tg :@: filter (not . isQTQualified) anns) ch
 where
   -- Generate fresh vars, run the action with the new, and restore the old
   withFreshTVE m = do
    newtve <- associateWithFreshvars tvs
    oldtve <- getTVE
    wrapWithTVE newtve oldtve m

   -- Run an action with a before- and after- var environment
   wrapWithTVE tveBefore tveAfter m = do
    modify (modTvarEnv $ const tveBefore)
    r <- m
    modify (modTvarEnv $ const tveAfter)
    return r

   -- Add fresh varIds for all existing varids
   associateWithFreshvars tvs = foldlM addFreshVar (return tvenv0) tvs
     where
       addFreshVar acc tv = do
         tvfresh <- newtv
         return $ tvext acc tv tvfresh

-- | Return a monomorphic polytype.
monomorphize :: (Monad m) => K3 QType -> m QPType
monomorphize t = return $ QPType [] t

-- | Generalization for let-polymorphism.
generalize :: TInfM (K3 QType) -> TInfM QPType
generalize ta = do
 tve_before <- getTVE
 t          <- ta
 tve_after  <- getTVE
 t'         <- tvsub t -- NOTE: why substitute? It just breaks links
 -- Check for free vars that have been captured after the action
 -- NOTE: Why do this? Why not just check for free vars?
 let tvdep = tvDependentSet (tvfree tve_before) tve_after
 -- get the set of free vars
 let fv    = filter (not . tvdep) $ varsIn t'
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

        subAnns (EQType qt) = tvsub qt >>= return . EQType
        subAnns x = return x

-- | Top-level type inference methods
inferProgramTypes :: K3 Declaration -> Either String (K3 Declaration)
inferProgramTypes prog = do
    -- Prepare the initial type environment
    (_, initEnv) <- let (a, b) = runTInfM tienv0 $ initializeTypeEnv
                    in a >>= return . (, b)
    nProg <- fst $ runTInfM initEnv $ mapProgram declF annMemF exprF prog
    return nProg
  where
    initializeTypeEnv :: TInfM (K3 Declaration)
    initializeTypeEnv = mapProgram initDeclF initAMemF initExprF prog

    -- Make sure certain identifiers don't already exist in the environment
    withUnique' :: (TIEnv -> a) -> String -> Identifier ->
                   TInfM (K3 Declaration) -> TInfM (K3 Declaration)
    withUnique' lookupF s n m = failOnValid (return ()) (uniqueErr s n)
                       (flip lookupF n) >>= const m

    withUnique n m  = withUnique' tilkupe "declaration"
    withUniqueA n m = withUnique' tilkupa "annotation"

    -- Fail on a successful application of a function
    failOnValid :: TInfM () -> TInfM () -> (TIEnv -> Either a b) -> TInfM ()
    failOnValid success failure f = do
      tienv <- get
      either (const $ success) (const $ failure) $ f tienv

    uniqueErr :: String -> Identifier -> TInfM a
    uniqueErr s n = left $ unwords ["Invalid unique", s, "identifier:", n]

    -- Create an initial declaration environment for recursive scope
    initDeclF :: K3 Declaration -> TInfM (K3 Declaration)
    initDeclF d@(tag -> DGlobal n t _)
      | isTFunction t = withUnique n $ do
          qpt <- qpType t
          modify (\env -> tiexte env n qpt)
          return d
      | otherwise     = return d

    initDeclF d@(tag -> DTrigger n t _) =
      withUnique n $ do
        qpt <- trigType t
        modify (\env -> tiexte env n qpt)
        return d
      where trigType x = do
        qt <- qType x
        monomorphize $ ttrg qt

    initDeclF d@(tag -> DAnnotation n tdeclvars mems) =
      withUniqueA n $ mkAnnMemEnv >> return d
      where mkAnnMemEnv = do
              l <- mapM memType mems
              modify $ \env ->
                tiexta env n $ HashMap.fromList catMaybes l

            memType (Lifted      _ nm typ _ _) = unifyMemInit True  nm typ
            memType (Attribute   _ nm typ _ _) = unifyMemInit False nm typ
            memType (MAnnotation _ _ _)       = return Nothing

            unifyMemInit lifted nm typ = do
              qpt <- qpType $ TC.forAll tdeclvars typ
              return $ Just (nm, (qpt, lifted))

    initDeclF d = return d

    initAMemF :: AnnMemDecl -> TInfM AnnMemDecl
    initAMemF mem  = return mem

    initExprF :: K3 Expression -> TInfM (K3 Expression)
    initExprF expr = return expr

    unifyInitializer :: Identifier -> Either (Maybe QPType) QPType -> Maybe (K3 Expression) -> TInfM (Maybe (K3 Expression))
    unifyInitializer n qptE eOpt = do
      qpt <- case qptE of
              Left (Nothing)   -> get >>= \env -> liftEitherM (tilkupe env n)
              Left (Just qpt') -> modify (\env -> tiexte env n qpt') >> return qpt'
              Right qpt'       -> return qpt'

      case eOpt of
        Just e -> do
          qt1 <- instantiate qpt
          qt2 <- qTypeOfM e
          void $ unifyWithOverrideM qt1 qt2 $ mkErrorF e unifyInitErrF
          substituteDeepQt e >>= return . Just

        Nothing -> return Nothing

    declF :: K3 Declaration -> TInfM (K3 Declaration)
    declF d@(tag -> DGlobal n t eOpt) = do
      qptE <- if isTFunction t then return (Left Nothing)
                               else (qpType t >>= return . Left . Just)
      if isTEndpoint t
        then return d
        else unifyInitializer n qptE eOpt >>= \neOpt ->
               return $ (Node (DGlobal n t neOpt :@: annotations d) $ children d)

    declF d@(tag -> DTrigger n t e) =
      get >>= \env -> liftEitherM (tilkupe env n) >>= \(QPType qtvars qt) ->
        case tag qt of
          QTCon QTTrigger -> let nqptE = Right $ QPType qtvars $ tfun (head $ children qt) tunit
                             in unifyInitializer n nqptE (Just e) >>= \neOpt ->
                                  return $ maybe d (\ne -> Node (DTrigger n t ne :@: annotations d) $ children d) neOpt
          _ -> trigTypeErr n

    declF d@(tag -> DAnnotation n tvars mems) =
        get >>= \env -> liftEitherM (tilkupa env n) >>= chkAnnMemEnv >>= \nmems ->
          return (Node (DAnnotation n tvars nmems :@: annotations d) $ children d)

      where chkAnnMemEnv amEnv = mapM (memType amEnv) mems

            memType amEnv (Lifted mp mn mt meOpt mAnns) =
              unifyMemInit amEnv mn meOpt >>= \nmeOpt -> return (Lifted mp mn mt nmeOpt mAnns)

            memType amEnv (Attribute   mp mn mt meOpt mAnns) =
              unifyMemInit amEnv mn meOpt >>= \nmeOpt -> return (Attribute mp mn mt nmeOpt mAnns)

            memType _ mem@(MAnnotation _ _ _) = return mem

            unifyMemInit amEnv mn meOpt = do
              qpt <- maybe (memLookupErr mn) (return . fst) (lookup mn amEnv)
              unifyInitializer mn (Right qpt) meOpt

    declF d = return d

    annMemF :: AnnMemDecl -> TInfM AnnMemDecl
    annMemF mem = return mem

    exprF :: K3 Expression -> TInfM (K3 Expression)
    exprF e = inferExprTypes e

    mkErrorF :: K3 Expression -> (String -> String) -> (String -> String)
    mkErrorF e f s = spanAsString ++ f s
      where spanAsString = let spans = mapMaybe getSpan $ annotations e
                           in if null spans
                                then (boxToString $ ["["] %+ prettyLines e %+ ["]"])
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

    mkErrorF :: K3 Expression -> (String -> String) -> (String -> String)
    mkErrorF e f s = spanAsString ++ f s
      where spanAsString = let spans = mapMaybe getSpan $ annotations e
                           in if null spans then (boxToString $ ["["] %+ prettyLines e %+ ["]"])
                                            else unwords ["[", show $ head spans, "] "]

    monoBinding :: Identifier -> K3 QType -> TInfM ()
    monoBinding i t = do
      mt <- monomorphize t
      modify (\env -> tiexte env i mt)

    lambdaBinding :: K3 Expression -> K3 Expression -> TInfM ()
    lambdaBinding _ (tag -> ELambda i) = newtv >>= monoBinding i
    lambdaBinding _ _ = return ()

    -- TODO: need to chase pointers in qTypeOfM
    sidewaysBinding :: K3 Expression -> K3 Expression -> TInfM [TInfM ()]

    sidewaysBinding ch1 (tag -> ELetIn i) = do
      ipt <- generalize $ qTypeOfM ch1
      modify $ \env -> tiexte env i ipt
      return [iu]

    sidewaysBinding ch1 (tag -> EBindAs b) = do
        ch1T <- qTypeOfM ch1
        case b of
          BIndirection id' -> do
            itv <- newtv
            void $ unifyM ch1T (tind itv) $ bindErr "indirection"
            monoBinding id' itv

          BTuple ids -> do
            idtvs <- mapM (const newtv) ids
            void   $ unifyM ch1T (ttup idtvs) $ bindErr "tuple"
            mapM_ (uncurry monoBinding) $ zip ids idtvs

          -- TODO: partial bindings?
          BRecord ijs -> do
            jtvs <- mapM (const newtv) ijs
            void $  unifyM ch1T (trec $ flip zip jtvs $ map fst ijs) $ bindErr "record"
            mapM_ (uncurry monoBinding) $ flip zip jtvs $ map snd ijs

        return [iu]

      where
        bindErr kind reason = unwords ["Invalid", kind, "bind-as:", reason]

    sidewaysBinding ch1 (tag -> ECaseOf i) = do
      ch1T <- qTypeOfM ch1
      itv  <- newtv
      void $  unifyM ch1T (topt itv) $ (("Invalid case-of source expression: ")++)
      return [monoBinding i itv, modify $ \env -> tidele env i]

    sidewaysBinding _ (children -> ch) = return (replicate (length ch - 1) iu)

    inferQType :: [K3 Expression] -> K3 Expression -> TInfM (K3 Expression)
    inferQType _ n@(tag -> EConstant (CBool   _)) = return $ n .+ tbool
    inferQType _ n@(tag -> EConstant (CByte   _)) = return $ n .+ tbyte
    inferQType _ n@(tag -> EConstant (CInt    _)) = return $ n .+ tint
    inferQType _ n@(tag -> EConstant (CReal   _)) = return $ n .+ treal
    inferQType _ n@(tag -> EConstant (CString _)) = return $ n .+ tstr

    inferQType _ n@(tag -> EConstant (CNone nm)) = do
      tv <- newtv
      let ntv = case nm of
                  NoneMut   -> mutQT tv
                  NoneImmut -> immutQT tv
      return $ n .+ (topt ntv)

    inferQType _ n@(tag -> EConstant (CEmpty t)) = do
      cqt <- qType t
      let annIds =  namedEAnnotations $ annotations n
      colqt <- mkCollectionQType annIds cqt
      return $ n .+ colqt

    -- | Variable specialization. Note that instantiate strips qualifiers.
    inferQType _ n@(tag -> EVariable i) = do
        env <- get
        qt  <- either (lookupError i) instantiate (tilkupe env i)
        return $ n .+ qt

    -- | Data structures. Qualifiers are taken from child expressions by rebuildE.
    -- TODO: actually they're not
    inferQType ch n@(tag -> ESome)       = qTypeOfM (head ch) >>=
                                             return . ((rebuildE n ch) .+) . topt
    inferQType ch n@(tag -> EIndirect)   = qTypeOfM (head ch) >>=
                                             return . ((rebuildE n ch) .+) . tind
    inferQType ch n@(tag -> ETuple)      = mapM qTypeOfM ch   >>=
                                             return . ((rebuildE n ch) .+) . ttup
    inferQType ch n@(tag -> ERecord ids) = mapM qTypeOfM ch   >>=
                                             return . ((rebuildE n ch) .+) . trec . zip ids

    -- | Lambda expressions are passed the post-processed environment,
    --   so the type variable for the identifier is bound in the type environment.
    inferQType ch n@(tag -> ELambda i) = do
        env  <- get
        ipt  <- either (lambdaBindingErr i) return $ tilkupe env i
        chqt <- qTypeOfM $ head ch
        void $ modify $ \env' -> tidele env' i
        case ipt of
          QPType [] iqt -> return $ rebuildE n ch .+ tfun iqt chqt
          _             -> polyLambdaBindingErr

    -- | Assignment expressions unify their source and target types, as well as
    --   ensuring that the source is mutable.
    inferQType ch n@(tag -> EAssign id') = do
      env <- get
      (ipt, muid) <- either (assignBindingErr id') return $ tilkupe env id'
      eqt <- qTypeOfM $ head ch
      case ipt of
        QPType [] iqt -- monomorphic
          | (iqt @~ isQTQualified) == Just QTMutable -> do
              void $ unifyM (iqt @- QTMutable) eqt $
                mkErrorF n (("Invalid assignment to " ++ id' ++ ": ") ++)
              return $ rebuildE n ch .+ tunit
          | otherwise -> mutabilityErr i

        _ -> polyAssignBindingErr

    inferQType ch n@(tag -> EProject id') = do
      srcqt   <- qTypeOfM $ head ch
      fieldqt <- newtv
      let prjqt = tlowerrec [(id', fieldqt)]
      void $ trace (prettyTaggedPair ("infer prj " ++ id') srcqt prjqt)
           $ unifyM srcqt prjqt $ mkErrorF n
             ((unlines ["Invalid record projection:", pretty srcqt, "and", pretty prjqt]) ++)
      return $ rebuildE n ch .+ fieldqt

    -- TODO: reorder inferred record fields based on argument at application.
    -- TODO: add applied lower/higher to concretization set
    -- TODO: don't force lower unification on lambda application
    inferQType ch n@(tag -> EOperate OApp) = do
      fnqt  <- qTypeOfM $ head ch
      argqt <- qTypeOfM $ last ch
      retqt <- newtv
      let errf = mkErrorF n (unlines ["Invalid function application:",
                                       pretty fnqt,
                                       "and",
                                       pretty (tfun argqt retqt), ":"] ++)
      void $ trace (prettyTaggedTriple "infer app " n fnqt $ tfun argqt retqt) $
        unifyWithOverrideM fnqt (tfun argqt retqt) errf
      return $ rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EOperate OSeq) = do
        lqt <- qTypeOfM $ head ch
        rqt <- qTypeOfM $ last ch
        void $ unifyM tunit lqt $ mkErrorF n (("Invalid left sequence operand: ") ++)
        return $ rebuildE n ch .+ rqt

    -- | Check trigger-address pair and unify trigger type and message argument.
    inferQType ch n@(tag -> EOperate OSnd) = do
        trgtv <- newtv
        void $ unifyBinaryM (ttup [ttrg trgtv, taddr]) trgtv ch n sndError
        return $ rebuildE n ch .+ tunit

    -- | Unify operand types based on the kind of operator.
    inferQType ch n@(tag -> EOperate op)
    -- TODO: deal with lower and numeric
      | numeric op = do
            (lqt, rqt) <- unifyBinaryM tnum tnum ch n numericError
            resultqt   <- delayNumericQt lqt rqt
            return $ rebuildE n ch .+ resultqt

      | comparison op = do
          lqt <- qTypeOfM $ head ch
          rqt <- qTypeOfM $ last ch
          void $ unifyM lqt rqt $ mkErrorF n comparisonError
          return $ rebuildE n ch .+ tbool

      | logic op = do
            void $ unifyBinaryM tbool tbool ch n logicError
            return $ rebuildE n ch .+ tbool

      | textual op = do
            void $ unifyBinaryM tstr tstr ch n stringError
            return $ rebuildE n ch .+ tstr

      | op == ONeg = do
            chqt <- unifyUnaryM tnum ch $ mkErrorF n uminusError
            let resultqt = case tag chqt of
                             QTPrimitive _  -> chqt
                             QTVar _ -> chqt
                             -- NOTE:?
                             _ -> tnum
            return $ rebuildE n ch .+ resultqt

      | op == ONot = do
            void $ unifyUnaryM tbool ch $ mkErrorF n negateError
            return $ rebuildE n ch .+ tbool

      | otherwise = left $ "Invalid operation: " ++ show op

      where
        delayNumericQt l r
          | or (map isQTVar   [l, r]) = return $ tlower [l,r]
          | or (map isQTLower [l, r]) = return $ tlower $
                                          concatMap childrenOrSelf [l,r]
          | otherwise = tvlower l r

        childrenOrSelf t@(tag -> QTOperator QTLower) = children t
        childrenOrSelf t = [t]

    -- First child generation has already been performed in sidewaysBinding
    -- Delete the parameter from the env as we leave this node
    inferQType ch n@(tag -> ELetIn j) = do
      bqt <- qTypeOfM $ last ch
      void $ modify $ \env -> tidele env j
      return $ rebuildE n ch .+ bqt

    -- First child unification has already been performed in sidewaysBinding
    -- Delete the parameters from the env as we leave this node
    inferQType ch n@(tag -> EBindAs b) = do
      bqt <- qTypeOfM $ last ch
      case b of
        BIndirection i -> modify $ \env -> tidele env i
        BTuple ids     -> modify $ \env -> foldl tidele env ids
        BRecord ids    -> modify $ \env -> foldl tidele env $ map snd ids
      return $ rebuildE n ch .+ bqt

    -- First child unification has already been performed in sidewaysBinding
    inferQType ch n@(tag -> ECaseOf _) = do
      sqt   <- qTypeOfM $ ch !! 1
      nqt   <- qTypeOfM $ last ch
      retqt <- unifyWithOverrideM sqt nqt $ mkErrorF n (("Mismatched case-of branch types: ") ++)
      return $ rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EIfThenElse) = do
      pqt   <- qTypeOfM $ head ch
      tqt   <- qTypeOfM $ ch !! 1
      eqt   <- qTypeOfM $ last ch
      void  $  unifyM pqt tbool $ mkErrorF n $ (("Invalid if-then-else predicate: ") ++)
      retqt <- unifyWithOverrideM tqt eqt $ mkErrorF n $ (("Mismatched condition branches: ") ++)
      return $ rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EAddress) = do
      hostqt <- qTypeOfM $ head ch
      portqt <- qTypeOfM $ last ch
      void $ unifyM hostqt tstr $ mkErrorF n $ (("Invalid address host string: ") ++)
      void $ unifyM portqt tint $ mkErrorF n $ (("Invalid address port int: ") ++)
      return $ rebuildE n ch .+ taddr

    inferQType ch n  = return $ rebuildE n ch
      -- ^ TODO unhandled: ESelf, EImperative

    rebuildE (Node t _) ch = Node t ch

    unifyBinaryM lexpected rexpected ch n errf = do
      lqt <- qTypeOfM $ head ch
      rqt <- qTypeOfM $ last ch
      void $ unifyM lexpected lqt (mkErrorF n $ errf "left")
      void $ unifyM rexpected rqt (mkErrorF n $ errf "right")
      return (lqt, rqt)

    unifyUnaryM expected ch errf = do
        chqt <- qTypeOfM $ head ch
        void $ unifyM chqt expected errf
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

-- Only allow record contents in this version of the type system
-- Make a collection qtype into the equivalent record
mkCollectionQType :: [Identifier] -> K3 QType -> TInfM (K3 QType)
mkCollectionQType annIds contentQt@(tag -> QTCon (QTRecord _)) =
  return $ tcol contentQt annIds
mkCollectionQType annIds contentQt@(tag -> QTOpen _ (QTCon (QTRecord _))) =
  return $ tcol contentQt annIds

mkCollectionQType _ qt = left $ "Invalid content record type: " ++ show qt


-- NOTE: how do we ever get self inside the self type?
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
    let (lifted, regular) = partition (snd . snd) flatEnvs
        (lifted', regular') = (removeBool lifted, removeBool regular)
    finalQt <- mkFinalQType contentQt regular
    selfQt  <- instantiateMembers lifted >>=
               subCTVars contentQt finalQt . trec
    return (finalQt, selfQt)
  where
    removeBool = map (second fst)

    mkFinalQType conQt regularMem =
      case tag conQt of
        QTCon (QTRecord ids) ->
           instantiateMembers regularMem >>=
             return . trec . ((zip ids $ children conQt) ++)
        _ -> nonRecordContentErr conQt

    -- Substitute for final and content types inside tree
    subCTVars content finalt tree = mapTree (subCF content finalt) tree
    subCF content _ _ (tag -> QTContent) = return content
    subCF _ finalt _  (tag -> QTFinal)   = return finalt
    subCF _ _ ch      (Node t _) = return $ Node t ch

    -- flatten all the member envs for a particular collection
    -- and find duplicate ids
    assertNoDuplicateIds =
      let flatEnvs = concat $ map $ HashMap.toList memEnvs
          ids      = map fst flatEnvs
      in if nub ids /= ids then nameConflictErr else return flatEnvs

    -- Convert collection members (qptypes) into a list of id, qtype
    -- qptypes are polymorphic
    instantiateMembers members = mapM (second instantiate) members

    nameConflictErr        =
      left $ "Conflicting annotation member names: " ++ show annIds
    nonRecordContentErr qt =
      left $ "Invalid content record type: " ++ show qt


{- Type conversion -}

qpType :: K3 Type -> TInfM QPType

-- | At top level foralls, we extend the declared var env in the type inference
--   environment with fresh qtype variables. This leads to substitutions for any
--   corresponding declared variables in the type tree.
qpType t@(tag -> TForall tvars) = do
  -- Create varIds for all the forall variables
  tvmap <- mapM idToNewVarId $ map (\(TypeVarDecl id' _ _) -> id') tvars
  -- Add and then delete the temporary forall identifiers
  void $ modify $ extend tvmap
  chQt <- qType (head $ children t)
  void $ modify $ prune tvmap
  return $ QPType (map snd tvmap) chQt

  where
    idToNewVarId id' = do
      v <- newtv
      vId <- varId v
      return (id', vId)
    extend tvmap env = foldl (\a (b,c) -> tiextdv a b c) env tvmap
    prune  tvmap env = foldl (\a (b,_) -> tideldv a b) env tvmap
    varId (tag -> QTVar i) = return i
    varId _ = left $ "Invalid type variable for type var bindings"

qpType t = generalize (qType t)
  -- Old code: qType t >>= monomorphize

-- | We currently do not support forall type quantifiers present at an
--   arbitrary location in the K3 Type tree since forall types are not
--   part of the QType datatype and grammar.
--   The above qpType method constructs polymorphic QTypes, which handles
--   top-level polymorphic types, creating mappings for declared variables
--   in a K3 Type to QType typevars.
--
qType :: K3 Type -> TInfM (K3 QType)
qType t = foldMapTree mkQType (ttup []) t >>= return . mutabilityT t
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

    mkQType _ (tag -> TForall _) = left $ "Invalid forall type for QType"
      -- ^ TODO: we can only handle top-level foralls, and not arbitrary
      --   foralls nested in type trees.

    mkQType _ t_ = left $ "No QType construction for " ++ show t_

    mutability0 nch n = mutabilityT (head $ children n) $ head nch
    mutabilityN nch n = map (uncurry mutabilityT) $ zip (children n) nch


-- | Converts all QType annotations on program expressions to K3 types.
translateProgramTypes :: K3 Declaration -> Either String (K3 Declaration)
translateProgramTypes prog = mapProgram declF annMemF exprF prog
  where declF   d = return d
        annMemF m = return m
        exprF   e = translateExprTypes e

translateExprTypes :: K3 Expression -> Either String (K3 Expression)
translateExprTypes expr = mapTree translate expr >>= \e -> return $ flip addTQualifier e $ exprTQualifier expr
  where
    translate nch e@(Node (tg :@: anns) _) = do
      let nch' = case tg of
                   ELetIn _ -> [flip addTQualifier (head nch) $ letTQualifier e] ++ tail nch
                   _        -> nch
      nanns <- mapM translateEQType $ filter (not . isEType) anns
      return (Node (tg :@: nanns) nch')

    addTQualifier tqOpt e@(Node (tg :@: anns) ch) = maybe e (\tq -> Node (tg :@: map (inject tq) anns) ch) tqOpt
      where inject tq (EType t) = maybe (EType $ t @+ tq) (const $ EType t) $ find isTQualified $ annotations t
            inject _ a = a

    letTQualifier  e = exprTQualifier $ head $ children e
    exprTQualifier e = maybe Nothing (Just . translateAnnotation) $ extractEQTypeQualifier e

    extractEQTypeQualifier e =
      case find isEQType $ annotations e of
        Just (EQType qt) -> find isQTQualified $ annotations qt
        _ -> Nothing

    translateEQType (EQType qt) = translateQType qt >>= return . EType
    translateEQType x = return x

    translateAnnotation a = case a of
      QTMutable   -> TMutable
      QTImmutable -> TImmutable
      QTWitness   -> TWitness


translateQType :: K3 QType -> Either String (K3 Type)
translateQType qt = mapTree translateWithMutability qt
  where translateWithMutability ch qt'@(tag -> QTCon tg)
          | tg `elem` [QTOption, QTIndirection, QTTuple] = translate (attachToChildren ch qt') qt'

        translateWithMutability ch qt'@(tag -> QTCon (QTRecord _)) = translate (attachToChildren ch qt') qt'

        translateWithMutability ch qt' = translate ch qt'

        attachToChildren ch qt' =
          map (uncurry $ foldl (@+)) $ zip ch $ map (map translateAnnotation . annotations) $ children qt'

        translateAnnotation a = case a of
          QTMutable   -> TMutable
          QTImmutable -> TImmutable
          QTWitness   -> TWitness

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

        translate ch (tag -> QTCon d) = case d of
          QTFunction          -> return $ TC.function (head ch) $ last ch
          QTOption            -> return $ TC.option $ head ch
          QTIndirection       -> return $ TC.indirection $ head ch
          QTTuple             -> return $ TC.tuple ch
          QTRecord        ids -> return $ TC.record $ zip ids ch
          QTCollection annIds -> return $ foldl (@+) (TC.collection $ head ch) $ map TAnnotation annIds
          QTTrigger           -> return $ TC.trigger $ head ch
          QTSource            -> return $ TC.source $ head ch
          QTSink              -> return $ TC.sink $ head ch

        translate _ qt' = Left $ "No translation for: " ++ show qt'


{- Instances -}
instance Pretty TIEnv where
  prettyLines (te, ta, tdv, tve) =
    ["TEnv: "]   %$ (indent 2 $ prettyLines te)  ++
    ["TAEnv: "]  %$ (indent 2 $ prettyLines ta)  ++
    ["TDVEnv: "] %$ (indent 2 $ prettyLines tdv) ++
    ["TVEnv: "]  %$ (indent 2 $ prettyLines tve)

instance Pretty TEnv where
  prettyLines te = prettyPairList te

instance Pretty TAEnv where
  prettyLines ta = Map.foldlWithKey (\acc k v -> acc ++ prettyPair (k,v)) [] ta

instance Pretty TMEnv where
  prettyLines tme = prettyPairList tme

instance Pretty TDVEnv where
  prettyLines tdve = prettyPairList tdve

instance Pretty TVEnv where
  prettyLines (TVEnv n m) = ["# vars: " ++ show n] ++
                            (Map.foldlWithKey (\acc k v -> acc ++ prettyPair (k,v)) [] m)

instance Pretty (QPType, Bool) where
  prettyLines (a,b) = (if b then ["(Lifted) "] else ["(Attr) "]) %+ prettyLines a

prettyPairList :: (Show a, Pretty b) => [(a,b)] -> [String]
prettyPairList l = foldl (\acc kvPair -> acc ++ prettyPair kvPair) [] l

prettyPair :: (Show a, Pretty b) => (a,b) -> [String]
prettyPair (a,b) = [show a ++ " => "] %+ prettyLines b

prettyTaggedSPair :: (Show a, Pretty b) => String -> a -> b -> String
prettyTaggedSPair s a b = boxToString $ [s ++ " " ++ show a] %+ [" and "] %+ prettyLines b

prettyTaggedPair :: (Pretty a, Pretty b) => String -> a -> b -> String
prettyTaggedPair s a b = boxToString $ [s ++ " "] %+ prettyLines a %+ [" and "] %+ prettyLines b

prettyTaggedTriple :: (Pretty a, Pretty b, Pretty c) => String -> a -> b -> c -> String
prettyTaggedTriple s a b c = boxToString $ [s ++ " "] %+ prettyLines a %+ [" "] %+ prettyLines b %+ [" and "] %+ prettyLines c
