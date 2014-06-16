{-# LANGUAGE LambdaCase #-}
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
module Language.K3.Analysis.HMTypes.Inference where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Either

import Data.Function
import Data.List
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe
import Data.Tree

import Language.K3.Core.Annotation
import Language.K3.Core.Common
import Language.K3.Core.Declaration
import Language.K3.Core.Expression
import Language.K3.Core.Type
import Language.K3.Core.Constructor.Type as TC
import Language.K3.Analysis.Common
import Language.K3.Analysis.HMTypes.DataTypes

-- | Misc. helpers
(.+) :: K3 Expression -> K3 QType -> K3 Expression
(.+) e qt = e @+ (EQType $ mutabilityE e qt)

infixr 5 .+

immutQT :: K3 QType -> K3 QType
immutQT = (@+ QTImmutable)

mutQT :: K3 QType -> K3 QType
mutQT = (@+ QTMutable)

mutabilityT :: K3 Type -> K3 QType -> K3 QType
mutabilityT t qt = case t @~ isTQualified of
                     Nothing -> qt
                     Just TImmutable -> immutQT qt
                     Just TMutable   -> mutQT qt
                     _ -> error "Invalid type qualifier annotation"

mutabilityE :: K3 Expression -> K3 QType -> K3 QType
mutabilityE e qt = case e @~ isEQualified of
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

projectNamedPairs :: [Identifier] -> [(Identifier, a)] -> [a]
projectNamedPairs ids idv = snd $ unzip $ filter (\(k,_) -> k `elem` ids) idv

rebuildNamedPairs :: [(Identifier, a)] -> [Identifier] -> [a] -> [a]
rebuildNamedPairs oldIdv newIds newVs = map (replaceNewPair $ zip newIds newVs) oldIdv
  where replaceNewPair pairs (k,v) = maybe v id $ lookup k pairs


-- | A type environment.
type TEnv = [(Identifier, QPType)]

-- | Annotation type environment.
type TAEnv = Map Identifier TMEnv

-- | Declared type variable environment.
type TDVEnv = [(Identifier, QTVarId)]

-- | Annotation member environment.
--   The boolean indicates whether the member is a lifted attribute.
type TMEnv = [(Identifier, (QPType, Bool))]

-- | A type variable environment.
data TVEnv = TVEnv QTVarId (Map QTVarId (K3 QType)) deriving Show

-- | A type inference environment.
type TIEnv = (TEnv, TAEnv, TDVEnv, TVEnv)

-- | The type inference monad
type TInfM = EitherT String (State TIEnv)

{- TEnv helpers -}
tenv0 :: TEnv
tenv0 = []

tlkup :: TEnv -> Identifier -> Either String QPType
tlkup env x = maybe err Right $ lookup x env 
 where err = Left $ "Unbound variable in type environment: " ++ x

text :: TEnv -> Identifier -> QPType -> TEnv
text env x t = (x,t) : env

tdel :: TEnv -> Identifier -> TEnv
tdel env x = deleteBy ((==) `on` fst) (x, QPType [] tint) env


{- TAEnv helpers -}
taenv0 :: TAEnv 
taenv0 = Map.empty

talkup :: TAEnv -> Identifier -> Either String TMEnv
talkup env x = maybe err Right $ Map.lookup x env
  where err = Left $ "Unbound variable in annotation environment: " ++ x

taext :: TAEnv -> Identifier -> TMEnv -> TAEnv
taext env x te = Map.insert x te env


{- TDVEnv helpers -}
tdvenv0 :: TDVEnv
tdvenv0 = []

tdvlkup :: TDVEnv -> Identifier -> Either String (K3 QType)
tdvlkup env x = maybe err (Right . tvar) $ lookup x env
  where err = Left $ "Unbound declared variable in environment: " ++ x

tdvext :: TDVEnv -> Identifier -> QTVarId -> TDVEnv
tdvext env x v = (x,v) : env

tdvdel :: TDVEnv -> Identifier -> TDVEnv
tdvdel env x = deleteBy ((==) `on` fst) (x,-1) env

{- TIEnv helpers -}
tienv0 :: TIEnv 
tienv0 = (tenv0, taenv0, tdvenv0, tvenv0)

-- | Getters.
tiee :: TIEnv -> TEnv
tiee (te,_,_,_) = te

tiae :: TIEnv -> TAEnv
tiae (_,ta,_,_) = ta

tidve :: TIEnv -> TDVEnv
tidve (_,_,tdv,_) = tdv

tive :: TIEnv -> TVEnv
tive (_,_,_,tv) = tv

-- | Modifiers.
mtiee :: (TEnv -> TEnv) -> TIEnv -> TIEnv
mtiee f (te,x,y,z) = (f te, x, y, z)

mtiae :: (TAEnv -> TAEnv) -> TIEnv -> TIEnv
mtiae f (x,ta,y,z) = (x, f ta, y, z)

mtidve :: (TDVEnv -> TDVEnv) -> TIEnv -> TIEnv
mtidve f (x,y,tdv,z) = (x, y, f tdv, z)

mtive :: (TVEnv -> TVEnv) -> TIEnv -> TIEnv
mtive f (x,y,z,tv) = (x, y, z, f tv)

tilkupe :: TIEnv -> Identifier -> Either String QPType
tilkupe (te,_,_,_) x = tlkup te x

tilkupa :: TIEnv -> Identifier -> Either String TMEnv
tilkupa (_,ta,_,_) x = talkup ta x

tilkupdv :: TIEnv -> Identifier -> Either String (K3 QType)
tilkupdv (_,_,tdv,_) x = tdvlkup tdv x

tiexte :: TIEnv -> Identifier -> QPType -> TIEnv
tiexte (te,ta,tdv,tv) x t = (text te x t, ta, tdv, tv)

tiexta :: TIEnv -> Identifier -> TMEnv -> TIEnv
tiexta (te,ta,tdv,tv) x ate = (te, taext ta x ate, tdv, tv) 

tiextdv :: TIEnv -> Identifier -> QTVarId -> TIEnv
tiextdv (te, ta, tdv, tv) x v = (te, ta, tdvext tdv x v, tv)

tidele :: TIEnv -> Identifier -> TIEnv
tidele (te,x,y,z) i = (tdel te i,x,y,z)

tideldv :: TIEnv -> Identifier -> TIEnv
tideldv (x,y,tdv,z) i = (x,y,tdvdel tdv i,z)

tiincrv :: TIEnv -> (QTVarId, TIEnv)
tiincrv (te, ta, tdv, TVEnv n s) = (n, (te, ta, tdv, TVEnv (succ n) s))


{- TVEnv helpers -}
tvenv0 :: TVEnv
tvenv0 = TVEnv 0 Map.empty

tvlkup :: TVEnv -> QTVarId -> Maybe (K3 QType)
tvlkup (TVEnv _ s) v = Map.lookup v s

tvext :: TVEnv -> QTVarId -> K3 QType -> TVEnv
tvext (TVEnv c s) v t = TVEnv c $ Map.insert v t s

-- TVE domain predicate: check to see if a TVarName is in the domain of TVE
tvdomainp :: TVEnv -> QTVarId -> Bool
tvdomainp (TVEnv _ s) v = Map.member v s

-- Give the list of all type variables that are allocated in TVE but
-- not bound there
tvfree :: TVEnv -> [QTVarId]
tvfree (TVEnv c s) = filter (\v -> not (Map.member v s)) [0..c-1]

-- `Shallow' substitution
tvchase :: TVEnv -> K3 QType -> K3 QType
tvchase tve (tag -> QTVar v) | Just t <- tvlkup tve v = tvchase tve t
tvchase _ t = t

-- 'Shallow' substitution, additionally returning the last variable in
--  the chased chain.
tvchasev :: TVEnv -> Maybe QTVarId -> K3 QType -> (Maybe QTVarId, K3 QType)
tvchasev tve _ (tag -> QTVar v) | Just ctv <- tvlkup tve v = tvchasev tve (Just v) ctv
tvchasev _ lastV tv = (lastV, tv)

-- Compute (quite unoptimally) the characteristic function of the set 
--  forall tvb \in fv(tve_before). Union fv(tvsub(tve_after,tvb))
tvdependentset :: TVEnv -> TVEnv -> (QTVarId -> Bool)
tvdependentset tve_before tve_after = 
    \tv -> any (\tvb -> occurs tv (tvar tvb) tve_after) tvbs
 where
   tvbs = tvfree tve_before

-- Return the list of type variables in t (possibly with duplicates)
freevars :: K3 QType -> [QTVarId]
freevars t = runIdentity $ foldMapTree extractVars [] t
  where
    extractVars _ (tag -> QTVar v) = return [v]
    extractVars chAcc _ = return $ concat chAcc

-- The occurs check: if v appears free in t
occurs :: QTVarId -> K3 QType -> TVEnv -> Bool
occurs v t@(tag -> QTCon _) tve = or $ map (flip (occurs v) tve) $ children t
occurs v (tag -> QTVar v2)  tve = maybe (v == v2) (flip (occurs v) tve) $ tvlkup tve v2
occurs _ _ _ = False


{- TInfM helpers -}

runTInfM :: TIEnv -> TInfM a -> (Either String a, TIEnv)
runTInfM env m = flip runState env $ runEitherT m

reasonM :: (String -> String) -> TInfM a -> TInfM a
reasonM errf = mapEitherT $ \m -> m >>= \case
  Left  err -> return . Left $ errf err
  Right r   -> return $ Right r

liftEitherM :: Either String a -> TInfM a
liftEitherM = either left return 

getTVE :: TInfM TVEnv
getTVE = get >>= return . tive

-- Allocate a fresh type variable
newtv :: TInfM (K3 QType)
newtv = do
  (nv, nenv) <- get >>= return . tiincrv
  put nenv
  return $ tvar nv


-- Deep substitute, throughout type structure
tvsub :: K3 QType -> TInfM (K3 QType)
tvsub qt = mapTree sub qt
  where
    sub ch t@(tag -> QTCon d) = return $ foldl (@+) (tdata d ch) $ annotations t

    sub ch t@(tag -> QTOperator QTLower)
      | null ch = left "Invalid qtype lower operator"
      | null $ concatMap freevars ch = tvopeval QTLower ch
      | otherwise = return $ foldl (@+) (tlower ch) $ annotations t

    sub _ t@(tag -> QTVar v) = getTVE >>= \tve ->
      case tvlkup tve v of
        Just t' -> tvsub t'
        _       -> return t

    sub _ t = return t

-- | Lower bound computation for numeric and record types.
--   This function does not preserve annotations.
tvlower :: K3 QType -> K3 QType -> TInfM (K3 QType)
tvlower a b = getTVE >>= \tve -> tvlower' (tvchase tve a) (tvchase tve b)
  where
    tvlower' a' b' = case (tag a', tag b') of
      (QTPrimitive p1, QTPrimitive p2)
        | [p1, p2] `intersect` [QTReal, QTInt, QTNumber] == [p1,p2] -> 
            return $ tprim $ toEnum $ minimum $ map fromEnum [p1,p2]
      
      (QTCon (QTRecord i1), QTCon (QTRecord i2)) 
        | i1 `intersect` i2 == i1 -> mergedRecord True  i1 a' i2 b'
        | i1 `intersect` i2 == i2 -> mergedRecord False i2 b' i1 a'
        | otherwise -> return $ trec $ nub $ zip (i1 ++ i2) $ (children a') ++ (children b')

      (QTCon (QTCollection _), QTCon (QTRecord _)) -> coveringCollection a' b'
      (QTCon (QTRecord _), QTCon (QTCollection _)) -> coveringCollection b' a'

      (_, _) -> lowerError a' b'

    mergedRecord subAsLeft subid subqt supid supqt = do
      fieldQt <- mergeCovering subAsLeft
                  (zip subid $ children subqt) (zip supid $ children supqt)
      return $ trec $ zip supid fieldQt

    mergeCovering subAsLeft sub sup =
      let lowerF = if subAsLeft then \supV subV -> tvlower subV supV
                                else \supV subV -> tvlower supV subV
      in mapM (\(k,v) -> maybe (return v) (lowerF v) $ lookup k sub) sup

    coveringCollection ct rt@(tag -> QTCon (QTRecord _)) =
      collectionSubRecord ct rt >>= \case
        Just _ -> return ct
        _      -> lowerError ct rt

    coveringCollection x y = lowerError x y

    lowerError x y = left $ unwords $ ["Invalid lower bound operands: ", show x, "and", show y]

-- | Type operator evaluation.
tvopeval :: QTOp -> [K3 QType] -> TInfM (K3 QType)
tvopeval _ [] = left $ "Invalid qt operator arguments"
tvopeval QTLower ch = foldM tvlower (head ch) $ tail ch

consistentTLower :: [K3 QType] -> TInfM (K3 QType)
consistentTLower ch =
    let (varCh, nonvarCh) = partition isQTVar $ nub ch in
    case (varCh, nonvarCh) of
      ([], []) -> left "Invalid lower qtype"
      ([], _)  -> return $ tlower $ nonvarCh
      (_, [])  -> getTVE >>= \tve -> unifiedLower (tail varCh) (tvchase tve $ head varCh)
      (_, _)   -> tvopeval QTLower nonvarCh >>= unifiedLower varCh
  where
    unifiedLower vch lb = do
      void $ mapM_ (extractAndUnifyV lb) vch
      return $ tlower $ [lb]++vch

    extractAndUnifyV t (tag -> QTVar v) = unifyv v t
    extractAndUnifyV _ _ = left "Invalid type var during lower qtype merge"

-- Unification helpers.
-- | Returns a self record and lifted attribute identifiers when given
--   a collection and a record that is a subtype of the collection.
collectionSubRecord :: K3 QType -> K3 QType -> TInfM (Maybe (K3 QType, [Identifier]))
collectionSubRecord ct@(tag -> QTCon (QTCollection annIds)) (tag -> QTCon (QTRecord ids))
  = get >>= mkColQT >>= return . testF
  where
    mkColQT tienv = do
      memEnvs <- mapM (liftEitherM . tilkupa tienv) annIds
      mkCollectionFSQType annIds memEnvs (last $ children ct)
    
    testF (_, self)
      | QTCon (QTRecord liftedAttrIds) <- tag self
      , liftedAttrIds `intersect` ids == ids
      = Just (self, liftedAttrIds)
    
    testF _ = Nothing

collectionSubRecord _ _ = return Nothing

-- Unify a free variable v1 with t2
unifyv :: QTVarId -> K3 QType -> TInfM ()
unifyv v1 t@(tag -> QTVar v2)
  | v1 == v2  = return ()
  | otherwise = modify $ mtive $ \tve -> tvext tve v1 t

unifyv v t = getTVE >>= \tve -> do
  if not $ occurs v t tve
    then modify $ mtive $ \tve' -> tvext tve' v t
    else tvsub t >>= \t' -> left $ unwords ["occurs check:", show v, "in", show t']

-- | Unification driver type synonyms.
type RecordParts = (K3 QType, QTData, [Identifier])
type QTypeCtor = [K3 QType] -> K3 QType
type UnifyPreF  a = K3 QType -> TInfM (a, K3 QType)
type UnifyPostF a = (a, a) -> K3 QType -> TInfM (K3 QType)

-- TODO: unification for QTSelf
-- | A unification driver, i.e., common unification code for both
--   our standard unification method, and unification with variable overrides
unifyDrv :: UnifyPreF a -> UnifyPostF a -> K3 QType -> K3 QType -> TInfM (K3 QType)
unifyDrv preF postF qt1 qt2 = do
    (p1, qt1') <- preF qt1
    (p2, qt2') <- preF qt2
    qt         <- unifyDrv' qt1' qt2'
    postF (p1, p2) qt

  where
    unifyDrv' :: K3 QType -> K3 QType -> TInfM (K3 QType)
    unifyDrv' t1@(isQTNumeric -> True) t2@(isQTNumeric -> True) = tvlower t1 t2

    unifyDrv' t1@(tag -> QTPrimitive p1) (tag -> QTPrimitive p2)
      | p1 == p2  = return t1
      | otherwise = primitiveErr p1 p2

    -- | Record subtyping for projection
    unifyDrv' t1@(tag -> QTCon d1@(QTRecord f1)) t2@(tag -> QTCon d2@(QTRecord f2))
      | f1 `intersect` f2 == f1 = onRecord (t1,d1,f1) (t2,d2,f2)
      | f1 `intersect` f2 == f2 = onRecord (t2,d2,f2) (t1,d1,f1)

    -- | Collection-as-record subtyping for projection
    unifyDrv' t1@(tag -> QTCon (QTCollection _)) t2@(tag -> QTCon (QTRecord _))
      = collectionSubRecord t1 t2 >>= \case
          Just (selfRecord, liftedAttrIds) -> onCollection selfRecord liftedAttrIds t1 t2
          _ -> unifyErr t1 t2 "collection-record" ""

    unifyDrv' t1@(tag -> QTCon (QTRecord _)) t2@(tag -> QTCon (QTCollection _))
      = collectionSubRecord t2 t1 >>= \case
          Just (selfRecord, liftedAttrIds) -> onCollection selfRecord liftedAttrIds t2 t1
          _ -> unifyErr t1 t2 "collection-record" ""

    unifyDrv' t1@(tag -> QTCon d1) t2@(tag -> QTCon d2) =
      onChildren d1 d2 "datatypes" (children t1) (children t2) (tdata d1)

    -- | Unification of a delayed LB operator applies to the lower bounds of each set.
    --   This returns a merged delayed LB operator containing all variables, and the lower
    --   bound of the non-variable elements.
    unifyDrv' t1@(tag -> QTOperator QTLower) t2@(tag -> QTOperator QTLower) = do
      lb1 <- lowerBound t1
      lb2 <- lowerBound t2
      void $ rcr lb1 lb2
      consistentTLower $ children t1 ++ children t2

    unifyDrv' tv@(tag -> QTVar v) t = unifyv v t >> return tv
    unifyDrv' t tv@(tag -> QTVar v) = unifyv v t >> return tv

    -- | Unification of a lower bound with a non-bound applies to the non-bound
    --   and the lower bound of the deferred set.
    --   This pattern match applies after type variable unification to allow typevars
    --   to match the lower-bound set.
    unifyDrv' t1@(tag -> QTOperator QTLower) t2 = do
      lb1 <- lowerBound t1
      void $ rcr lb1 t2
      consistentTLower $ children t1 ++ [t2]

    unifyDrv' t1 t2@(tag -> QTOperator QTLower) = do
      lb2 <- lowerBound t2
      void $ rcr t1 lb2
      consistentTLower $ [t1] ++ children t2

    -- | Top unifies with any value. Bottom unifies with only itself.
    unifyDrv' t1@(tag -> tg1) t2@(tag -> tg2)
      | tg1 == QTTop = return t2
      | tg2 == QTTop = return t1
      | tg1 == tg2   = return t1
      | otherwise    = unifyErr t1 t2 "qtypes" ""

    rcr :: K3 QType -> K3 QType -> TInfM (K3 QType)
    rcr a b = unifyDrv preF postF a b

    onCollection :: K3 QType -> [Identifier] -> K3 QType -> K3 QType -> TInfM (K3 QType)
    onCollection sQt liftedAttrIds 
                 ct@(tag -> QTCon ccon@(QTCollection _)) rt@(tag -> QTCon (QTRecord ids))
      = do
          let selfPairs   = zip liftedAttrIds $ children sQt
          let projSelfT   = projectNamedPairs ids selfPairs
          let tdcon       = QTRecord liftedAttrIds
          let errk        = "collection subtype" 
          let colCtor nch = tdata ccon $ (init $ children ct) ++
                              [tdata tdcon $ rebuildNamedPairs selfPairs ids nch]
          onChildren tdcon tdcon errk projSelfT (children rt) colCtor

    onCollection _ _ ct rt =
      left $ unwords ["Invalid collection arguments", show ct, "and", show rt]
    
    onRecord :: RecordParts -> RecordParts -> TInfM (K3 QType)
    onRecord (subT, subCon, subIds) (supT, supCon, supIds) =
      let supPairs    = zip supIds $ children supT
          supProjT    = projectNamedPairs subIds $ supPairs
          errk        = "record subtype"
          recCtor nch = tdata supCon $ rebuildNamedPairs supPairs subIds nch
      in onChildren subCon subCon errk (children subT) supProjT recCtor

    onChildren :: QTData -> QTData -> String -> [K3 QType] -> [K3 QType] -> QTypeCtor -> TInfM (K3 QType)
    onChildren tga tgb kind a b ctor
      | tga == tgb = onList a b ctor $ \s -> unifyErr tga tgb kind s
      | otherwise  = unifyErr tga tgb kind ""

    onList :: [K3 QType] -> [K3 QType] -> QTypeCtor -> (String -> TInfM (K3 QType)) -> TInfM (K3 QType)
    onList a b ctor errf =
      if length a == length b
        then mapM (uncurry rcr) (zip a b) >>= return . ctor
        else errf "Unification mismatch on lists."

    lowerBound t = tvopeval QTLower $ children t

    primitiveErr a b = unifyErr a b "primitives" ""
    unifyErr a b kind s = left $ unwords ["Unification mismatch on ", kind, ": ", show a, "and", show b, "(", s, ")"]

-- | Type unification.
unifyM :: K3 QType -> K3 QType -> (String -> String) -> TInfM ()
unifyM t1 t2 errf = reasonM errf $ void $ unifyDrv preChase postId t1 t2
  where preChase qt = getTVE >>= \tve -> return (Nothing, tvchase tve qt)
        postId _ qt = return qt

-- | Type unification with variable overrides to the unification result.
unifyWithOverrideM :: K3 QType -> K3 QType -> (String -> String) -> TInfM (K3 QType)
unifyWithOverrideM qt1 qt2 errf = reasonM errf $ unifyDrv preChase postUnify qt1 qt2
  where preChase qt = getTVE >>= \tve -> return $ tvchasev tve Nothing qt
        postUnify (v1, v2) qt = do
          let vs = catMaybes [v1, v2]
          void $ mapM_ (flip unifyv qt) vs
          return $ if null vs then qt else (tvar $ head vs)


-- | Given a polytype, for every polymorphic type var, replace all of
--   its occurrences in t with a fresh type variable. We do this by
--   creating a substitution tve and applying it to t.
--   We also strip any mutability qualifiers here since we only instantiate
--   on variable access.
instantiate :: QPType -> TInfM (K3 QType)
instantiate (QPType tvs t) = withFreshTVE $ do
  (Node (tg :@: anns) ch) <- tvsub t
  return $ Node (tg :@: filter (not . isQTQualified) anns) ch
 where
   wrapWithTVE tve_before tve_after m =
    modify (mtive $ const tve_before) >> m >>= \r -> modify (mtive $ const tve_after) >> return r

   withFreshTVE m = do
    ntve <- associate_with_freshvars tvs
    otve <- getTVE
    wrapWithTVE ntve otve m

   associate_with_freshvars [] = return tvenv0
   associate_with_freshvars (tv:rtvs) = do
     tve     <- associate_with_freshvars rtvs
     tvfresh <- newtv
     return $ tvext tve tv tvfresh

-- | Return a monomorphic polytype.
monomorphize :: (Monad m) => K3 QType -> m QPType
monomorphize t = return $ QPType [] t

-- | Generalization for let-polymorphism.
generalize :: TInfM (K3 QType) -> TInfM QPType
generalize ta = do
 tve_before <- getTVE
 t          <- ta
 tve_after  <- getTVE
 t'         <- tvsub t
 let tvdep = tvdependentset tve_before tve_after
 let fv    = filter (not . tvdep) $ nub $ freevars t'
 return $ QPType fv t 
 -- ^ We return an unsubstituted type to preserve type variables
 --   for late binding based on overriding unification performed
 --   in function application.
 --   Old implementation: return $ QPType fv t'

inferProgramTypes :: K3 Declaration -> Either String (K3 Declaration)
inferProgramTypes prog = do
    (_, initEnv) <- let (a,b) = runTInfM tienv0 $ initializeTypeEnv
                    in a >>= return . (, b)
    nProg <- fst $ runTInfM initEnv $ mapProgram declF annMemF exprF prog
    return nProg
  where
    initializeTypeEnv :: TInfM (K3 Declaration)
    initializeTypeEnv = mapProgram initDeclF initAMemF initExprF prog

    initDeclF :: K3 Declaration -> TInfM (K3 Declaration)
    initDeclF d@(tag -> DGlobal n t _) 
      | isTFunction t = qpType t >>= \qpt -> modify (\env -> tiexte env n qpt) >> return d
      | otherwise     = return d
    
    initDeclF d@(tag -> DTrigger n t _) =
      trigType t >>= \qpt -> modify (\env -> tiexte env n qpt) >> return d
      where trigType x = qType x >>= \qt -> return (ttrg qt) >>= monomorphize

    initDeclF d@(tag -> DAnnotation n tdeclvars mems) = mkAnnMemEnv >> return d
      where mkAnnMemEnv = mapM memType mems >>= \l -> modify (\env -> tiexta env n $ catMaybes l)
            memType (Lifted      _ mn mt _ _) = unifyMemInit True  mn mt
            memType (Attribute   _ mn mt _ _) = unifyMemInit False mn mt
            memType (MAnnotation _ _ _) = return Nothing
            unifyMemInit lifted mn mt = do
              qpt <- qpType (TC.forAll tdeclvars mt)
              return (Just (mn, (qpt, lifted)))

    initDeclF d = return d

    initAMemF :: AnnMemDecl -> TInfM AnnMemDecl
    initAMemF mem  = return mem

    initExprF :: K3 Expression -> TInfM (K3 Expression)
    initExprF expr = return expr

    unifyInitializer :: Identifier -> Either (Maybe QPType) QPType -> Maybe (K3 Expression) -> TInfM ()
    unifyInitializer n qptE eOpt = do
      qpt <- case qptE of
              Left (Nothing)   -> get >>= \env -> liftEitherM (tilkupe env n)
              Left (Just qpt') -> modify (\env -> tiexte env n qpt') >> return qpt'
              Right qpt'       -> return qpt'
      
      case (qpt, eOpt) of
        (QPType [] qt1, Just e) -> do
          qt2 <- qTypeOfM e
          unifyM qt1 qt2 unifyInitErrF

        (_, Nothing) -> return ()
        (_, _) -> polyTypeErr

    declF :: K3 Declaration -> TInfM (K3 Declaration)
    declF d@(tag -> DGlobal n t eOpt) = do
      qptE <- if isTFunction t then return (Left Nothing)
                               else (qpType t >>= return . Left . Just)
      if isTEndpoint t then return d
                       else unifyInitializer n qptE eOpt >> return d

    declF d@(tag -> DTrigger n _ e) =
      get >>= \env -> liftEitherM (tilkupe env n) >>= \(QPType qtvars qt) -> 
        case tag qt of
          QTCon QTTrigger -> let nqptE = Right $ QPType qtvars $ tfun (head $ children qt) tunit
                             in unifyInitializer n nqptE (Just e) >> return d
          _ -> trigTypeErr n
    
    declF d@(tag -> DAnnotation n _ mems) =
        get >>= \env -> liftEitherM (tilkupa env n) >>= chkAnnMemEnv >> return d
      where chkAnnMemEnv amEnv = mapM_ (memType amEnv) mems
            memType amEnv (Lifted      _ mn _ meOpt _) = unifyMemInit amEnv mn meOpt
            memType amEnv (Attribute   _ mn _ meOpt _) = unifyMemInit amEnv mn meOpt
            memType _ (MAnnotation _ _ _) = return ()
            unifyMemInit amEnv mn meOpt = do
              qpt <- maybe (memLookupErr mn) (return . fst) (lookup mn amEnv)
              unifyInitializer mn (Right qpt) meOpt

    declF d = return d

    annMemF :: AnnMemDecl -> TInfM AnnMemDecl
    annMemF mem = return mem

    exprF :: K3 Expression -> TInfM (K3 Expression)
    exprF e = inferExprTypes e

    memLookupErr  n = left $ "No annotation member in initial environment: " ++ n
    polyTypeErr     = left $ "Invalid polymorphic declaration type"
    trigTypeErr   n = left $ "Invlaid trigger declaration type for: " ++ n
    unifyInitErrF s = "Failed to unify initializer: " ++ s


inferExprTypes :: K3 Expression -> TInfM (K3 Expression)
inferExprTypes expr = do
    nexpr <- mapIn1RebuildTree lambdaBinding sidewaysBinding inferQType expr
    exprQtSub nexpr

  where
    iu :: TInfM ()
    iu = return ()

    -- | Replaces any type variables in a QType annotation on any subexpression.
    exprQtSub :: K3 Expression -> TInfM (K3 Expression)
    exprQtSub e = mapTree subNode e
      where subNode ch (Node (tg :@: anns) _) = do
              nanns <- mapM subAnns anns 
              return (Node (tg :@: nanns) ch)
            
            subAnns (EQType qt) = tvsub qt >>= return . EQType
            subAnns x = return x

    monoBinding :: Identifier -> K3 QType -> TInfM ()
    monoBinding i t = monomorphize t >>= \mt -> modify (\env -> tiexte env i mt)

    lambdaBinding :: K3 Expression -> K3 Expression -> TInfM ()
    lambdaBinding _ (tag -> ELambda i) = newtv >>= monoBinding i
    lambdaBinding _ _ = return ()

    sidewaysBinding :: K3 Expression -> K3 Expression -> TInfM [TInfM ()]
    sidewaysBinding ch1 (tag -> ELetIn i) = do
      ipt <- generalize $ qTypeOfM ch1
      modify $ \env -> tiexte env i ipt
      return [iu]

    sidewaysBinding ch1 (tag -> EBindAs b) = do
        ch1T <- qTypeOfM ch1
        case b of
          BIndirection i -> do
            itv <- newtv
            void $ unifyM ch1T (tind itv) $ bindErr "indirection"
            monoBinding i itv
          
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
      let ntv = case nm of { NoneMut -> mutQT tv; NoneImmut -> immutQT tv }
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
    inferQType ch n@(tag -> ESome)       = qTypeOfM (head ch) >>= return . ((rebuildE n ch) .+) . topt
    inferQType ch n@(tag -> EIndirect)   = qTypeOfM (head ch) >>= return . ((rebuildE n ch) .+) . tind
    inferQType ch n@(tag -> ETuple)      = mapM qTypeOfM ch   >>= return . ((rebuildE n ch) .+) . ttup 
    inferQType ch n@(tag -> ERecord ids) = mapM qTypeOfM ch   >>= return . ((rebuildE n ch) .+) . trec . zip ids

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
    inferQType ch n@(tag -> EAssign i) = do
      env <- get
      ipt <- either (assignBindingErr i) return $ tilkupe env i
      eqt <- qTypeOfM $ head ch
      case ipt of 
        QPType [] iqt
          | (iqt @~ isQTQualified) == Just QTMutable ->
              do { void $ unifyM iqt eqt (("Invalid assignment to " ++ i ++ ": ") ++);
                   return $ rebuildE n ch .+ tunit }
          | otherwise -> mutabilityErr i

        _ -> polyAssignBindingErr

    inferQType ch n@(tag -> EProject i) = do
      srcqt   <- qTypeOfM $ head ch
      fieldqt <- newtv
      void    $  unifyM srcqt (tlower $ [trec [(i, fieldqt)]]) (("Invalid record projection: ")++)
      return  $  rebuildE n ch .+ fieldqt

    -- TODO: reorder inferred record fields based on argument at application.
    inferQType ch n@(tag -> EOperate OApp) = do
      fnqt   <- qTypeOfM $ head ch
      argqt  <- qTypeOfM $ last ch
      retqt  <- newtv
      void   $  unifyWithOverrideM fnqt (tfun argqt retqt) (("Invalid function application: ") ++)
      return $  rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EOperate OSeq) = do
        lqt <- qTypeOfM $ head ch
        rqt <- qTypeOfM $ last ch
        void $ unifyM tunit lqt (("Invalid left sequence operand: ") ++)
        return $ rebuildE n ch .+ rqt

    -- | Check trigger-address pair and unify trigger type and message argument.
    inferQType ch n@(tag -> EOperate OSnd) = do
        trgtv <- newtv
        void $ unifyBinaryM (ttup [ttrg trgtv, taddr]) trgtv ch sndError
        return $ rebuildE n ch .+ tunit

    -- | Unify operand types based on the kind of operator.
    inferQType ch n@(tag -> EOperate op) 
      | numeric op = do
            (lqt, rqt) <- unifyBinaryM tnum tnum ch numericError
            resultqt   <- delayNumericQt lqt rqt
            return $ rebuildE n ch .+ resultqt

      | comparison op = do
          lqt <- qTypeOfM $ head ch
          rqt <- qTypeOfM $ last ch
          void $ unifyM lqt rqt comparisonError
          return $ rebuildE n ch .+ tbool

      | logic op = do
            void $ unifyBinaryM tbool tbool ch logicError
            return $ rebuildE n ch .+ tbool

      | textual op = do
            void $ unifyBinaryM tstr tstr ch stringError
            return $ rebuildE n ch .+ tstr

      | op == ONeg = do
            chqt <- unifyUnaryM tnum ch uminusError
            let resultqt = case tag chqt of
                             QTPrimitive _  -> chqt
                             QTVar _ -> chqt
                             _ -> tnum
            return $ rebuildE n ch .+ resultqt

      | op == ONot = do
            void $ unifyUnaryM tbool ch negateError
            return $ rebuildE n ch .+ tbool

      | otherwise = left $ "Invalid operation: " ++ show op

      where 
        delayNumericQt l r
          | or (map isQTVar   [l, r]) = return $ tlower [l,r]
          | or (map isQTLower [l, r]) = return $ tlower $ concatMap childrenOrSelf [l,r]
          | otherwise = tvlower l r

        childrenOrSelf t@(tag -> QTOperator QTLower) = children t
        childrenOrSelf t = [t]

    -- First child generation has already been performed in sidewaysBinding
    inferQType ch n@(tag -> ELetIn j) = do
      bqt <- qTypeOfM $ last ch
      void $ modify $ \env -> tidele env j
      return $ rebuildE n ch .+ bqt
    
    -- First child unification has already been performed in sidewaysBinding
    inferQType ch n@(tag -> EBindAs b) = do
      bqt <- qTypeOfM $ last ch
      case b of
        BIndirection i -> modify $ \env -> tidele env i
        BTuple ids     -> modify $ \env -> foldl tidele env ids
        BRecord ijs    -> modify $ \env -> foldl tidele env $ map snd ijs
      return $ rebuildE n ch .+ bqt
    
    -- First child unification has already been performed in sidewaysBinding
    inferQType ch n@(tag -> ECaseOf _) = do
      sqt   <- qTypeOfM $ ch !! 1
      nqt   <- qTypeOfM $ last ch
      retqt <- unifyWithOverrideM sqt nqt (("Mismatched case-of branch types: ") ++)
      return $ rebuildE n ch .+ retqt

    inferQType ch n@(tag -> EIfThenElse) = do
      pqt   <- qTypeOfM $ head ch
      tqt   <- qTypeOfM $ ch !! 1
      eqt   <- qTypeOfM $ last ch
      void  $  unifyM pqt tbool $ (("Invalid if-then-else predicate: ") ++)
      retqt <- unifyWithOverrideM tqt eqt $ (("Mismatched condition branches: ") ++)
      return $ rebuildE n ch .+ retqt

    inferQType _ n@(tag -> EAddress) = return $ n .+ taddr

    inferQType ch n  = return $ rebuildE n ch
      -- ^ TODO unhandled: ESelf, EImperative

    rebuildE (Node t _) ch = Node t ch

    unifyBinaryM lexpected rexpected ch errf = do
      lqt <- qTypeOfM $ head ch
      rqt <- qTypeOfM $ last ch
      void $ unifyM lexpected lqt (errf "left")
      void $ unifyM rexpected rqt (errf "right")
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

mkCollectionQType :: [Identifier] -> K3 QType -> TInfM (K3 QType)
mkCollectionQType annIds contentQt@(tag -> QTCon (QTRecord _)) = return $ tcol contentQt annIds
mkCollectionQType _ qt = left $ "Invalid content record type: " ++ show qt

mkCollectionFSQType :: [Identifier] -> [TMEnv] -> K3 QType -> TInfM (K3 QType, K3 QType)
mkCollectionFSQType annIds memEnvs contentQt = do
    flatEnvs <- assertNoDuplicateIds
    let (lifted, regular) = partition (snd . snd) flatEnvs
    finalQt <- mkFinalQType contentQt regular
    selfQt  <- subCTVars contentQt finalQt $ trec $ membersAsRecordFields lifted
    return (finalQt, selfQt)
  where 
    mkFinalQType cqt regular =
      case tag cqt of
        QTCon (QTRecord ids) ->
           return $ trec $ (zip ids $ children cqt) ++ (membersAsRecordFields regular)
        _ -> nonRecordContentErr cqt

    subCTVars ct ft st = mapTree (subCF ct ft) st
    subCF ct _ _ (tag -> QTContent) = return ct
    subCF _ ft _ (tag -> QTFinal)   = return ft
    subCF _ _ ch (Node t _) = return $ Node t ch

    assertNoDuplicateIds = 
      let flatEnvs = concat memEnvs
          ids      = map fst flatEnvs
      in if nub ids /= ids then nameConflictErr else return flatEnvs
    
    membersAsRecordFields attrs = map (\(j,(QPType _ qt,_)) -> (j,qt)) attrs 
      -- ^ TODO: handle free vars?

    nameConflictErr        = left $ "Conflicting annotation member names: " ++ show annIds
    nonRecordContentErr qt = left $ "Invalid content record type: " ++ show qt


{- Type conversion -}

qpType :: K3 Type -> TInfM QPType

-- | At top level foralls, we extend the declared var env in the type inference
--   environment with fresh qtype variables. This leads to substitutions for any
--   corresponding declared variables in the type tree.
qpType t@(tag -> TForall tvars) = do
  tvmap <- mapM (\(TypeVarDecl i _ _) -> newtv >>= varId >>= return . (i,)) tvars
  void $ modify $ extend tvmap
  chQt <- qType (head $ children t)
  void $ modify $ prune tvmap
  return $ QPType (map snd tvmap) chQt

  where
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

    mkQType _ (tag -> TDeclaredVar x) = get >>= \tienv -> liftEitherM (tilkupdv tienv x)

    mkQType _ (tag -> TForall _) = left $ "Invalid forall type for QType"
      -- ^ TODO: we can only handle top-level foralls, and not arbitrary
      --   foralls nested in type trees.

    mkQType _ t_ = left $ "No QType construction for " ++ show t_

    mutability0 nch n = mutabilityT (head $ children n) $ head nch
    mutabilityN nch n = map (uncurry mutabilityT) $ zip (children n) nch
