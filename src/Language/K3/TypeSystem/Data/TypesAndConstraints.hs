{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, ConstraintKinds, ScopedTypeVariables, FlexibleInstances #-}

module Language.K3.TypeSystem.Data.TypesAndConstraints
( TVarQualification(..)
, TVar(..)
, tvarId
, ConstraintSetType
, TVarOrigin(..)
, QVar
, UVar
, AnyTVar(..)
, onlyUVar
, onlyQVar
, someVar
, TQual(..)
, allQuals
, QuantType(..)
, NormalQuantType
, AnnType(..)
, NormalAnnType
, AnnBodyType(..)
, NormalAnnBodyType
, AnnMemType(..)
, NormalAnnMemType
, MorphismArity(..)
, OpaqueID(..)
, OpaqueOrigin(..)
, OpaqueVar(..)
, ShallowType(..)
, TPolarity(..)
, TEnv
, TEnvId(..)
, TypeAliasEntry(..)
, NormalTypeAliasEntry
, TQuantEnvValue
, TAliasEnv
, TNormEnv
, TParamEnv
, TQuantEnv
, TGlobalQuantEnv
, TypeOrVar
, QualOrVar
, UVarBound
, BinaryOperator(..)
, AnyOperator(..)
, Constraint(..)
, ConstraintSet(..)
) where

import Data.Function
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set

import Language.K3.Core.Common
import Language.K3.Pretty
import Language.K3.TypeSystem.Data.Coproduct

-- * Types

data TVarQualification
  = UnqualifiedTVar
  | QualifiedTVar
  deriving (Eq, Ord, Read, Show)

-- TODO: change TVar arguments so that origin is first (for consistency)

-- |A data structure representing type variables.  The first argument for each
--  constructor is an index uniquely identifying the type variable.   The
--  second is an origin describing why the type variable was created (for
--  history and tracking purposes).
data TVar (a :: TVarQualification) where
  QTVar :: Int
        -> TVarOrigin QualifiedTVar
        -> TVar QualifiedTVar
  UTVar :: Int
        -> TVarOrigin UnqualifiedTVar
        -> TVar UnqualifiedTVar

instance Pretty (TVar a) where
  prettyLines v = case v of
    QTVar n _ -> ["å" ++ show n]
    UTVar n _ -> ["α" ++ show n]

tvarId :: TVar a -> Int
tvarId a = case a of
            QTVar n _ -> n
            UTVar n _ -> n

instance Eq (TVar a) where
  (==) = (==) `on` tvarId
instance Ord (TVar a) where
  compare = compare `on` tvarId
deriving instance Show (TVar a)

-- |A constraint kind describing the constraints pap
type ConstraintSetType c = (Pretty c, Show c)

-- |A description of the origin of a given type variable.
data TVarOrigin (a :: TVarQualification)
  = TVarSourceOrigin UID -- ^Type variable produced directly from source code.
  | TVarPolyinstantiationOrigin (TVar a) UID
      -- ^Type variable is the result of polyinstantiation at a given node UID.
  | TVarBoundGeneralizationOrigin [TVar a] TPolarity
      -- ^Type variable was created to generalize a number of existing
      --  variables.  The polarity describes the bounding direction: positive
      --  if this variable will be a lower bound, negative if it will be an
      --  upper bound.
  | TVarAlphaRenamingOrigin (TVar a)
      -- ^Type variable was created to provide an alpha renaming of another
      --  variable in order to ensure that the variables were distinct.
  | forall c. (ConstraintSetType c)
    => TVarCollectionInstantiationOrigin (AnnType c) UVar
      -- ^The type variable was created as part of the instantiation of a
      --  collection type.
  | forall c. (ConstraintSetType c)
    => TVarAnnotationToFunctionOrigin (AnnType c)
      -- ^Type variable was created to model an annotation as a function for the
      --  purposes of subtyping.
  | TVarEmptyAnnotationOrigin
      -- ^Type variable was created to represent a fresh empty annotation
      --  (which is used when annotations are concatenated).
  | TVarAnnotationFreshenOrigin (TVar a) UID
      -- ^Type variable was the result of polyinstantiation of variables in an
      --  annotation type at a given node UID.
  | TVarAnnotationDeclaredParamOrigin UID Identifier
      -- ^Type variable was declared on an annotation and constructed during
      --  type decision.  The UID identifies the annotation; the identifier
      --  names the declared type variable.

deriving instance Show (TVarOrigin a)

-- |A type alias for qualified type variables.
type QVar = TVar QualifiedTVar
-- |A type alias for unqualified type variables.
type UVar = TVar UnqualifiedTVar

-- |A data type which carries any type of type variable.
data AnyTVar
  = SomeQVar QVar
  | SomeUVar UVar
  deriving (Eq, Ord, Show)

instance Pretty AnyTVar where
  prettyLines sa = case sa of
                    SomeQVar qa -> prettyLines qa
                    SomeUVar a -> prettyLines a

-- |A function to match only qualified type variables.
onlyQVar :: AnyTVar -> Maybe QVar
onlyQVar sa = case sa of
  SomeQVar qa -> Just qa
  SomeUVar _ -> Nothing
-- |A function to match only unqualified type variables.
onlyUVar :: AnyTVar -> Maybe UVar
onlyUVar sa = case sa of
  SomeQVar _ -> Nothing
  SomeUVar a -> Just a

someVar :: TVar a -> AnyTVar
someVar a = case a of
  QTVar{} -> SomeQVar a
  UTVar{} -> SomeUVar a

-- |Type qualifiers.
data TQual = TMut | TImmut
  deriving (Eq, Ord, Read, Show)

instance Pretty TQual where
  prettyLines q = case q of
                    TMut -> ["mut"]
                    TImmut -> ["immut"]

instance Pretty (Set TQual) where
  prettyLines qs =
    ["{"] %+ intersperseBoxes [","] (map prettyLines $ Set.toList qs) %+ ["}"]
  
-- |A set of all qualifiers.
allQuals :: Set TQual
allQuals = Set.fromList [TMut, TImmut]

-- |Quantified types.  The constraint set type is left parametric for later use
--  by the environment decision procedure.
data QuantType c
  = QuantType (Set AnyTVar) QVar c
      -- ^Constructs a quantified type.  The arguments are the set of variables
      --  over which the type is polymorphic, the variable describing the type,
      --  and the set of constraints on that variable
  deriving (Eq, Ord, Show)

instance (Pretty c) => Pretty (QuantType c) where
  prettyLines (QuantType sas qa cs) =
    ["∀{"] %+
    sequenceBoxes maxWidth "," (map prettyLines $ Set.toList sas) %+
    ["}. "] %+
    prettyLines qa %+
    ["\\"] %/
    prettyLines cs
  
-- |A type alias for normal quantified types (which use normal constraint sets).
type NormalQuantType = QuantType ConstraintSet

-- |Annotation types.  The constraint set type is left parametric for later use
--  by the environment decision procedure.
data AnnType c
  = AnnType TParamEnv (AnnBodyType c) c
      -- ^Constructs an annotation type.  The arguments are the named parameter
      --  bindings for the annotation type, the body of the annotation type, and
      --  the set of constraints which apply to that body.
  deriving (Eq, Ord, Show)

instance (Pretty c) => Pretty (AnnType c) where
  prettyLines (AnnType p b cs) =
    ["Λ"] %+ prettyMap p +% ["."] %$ prettyLines b +% ["\\"] %$ prettyLines cs
    where
      prettyMap m = sequenceBoxes maxWidth "," $
                      map prettyElem $ Map.toList m
      prettyElem (k,v) = prettyLines k %+ ["→"] %+ prettyLines v
  
-- |A type alias for normal annotation types (which use normal constraint sets).
type NormalAnnType = AnnType ConstraintSet

-- |Annotation body types.  The type parameter dictates the type of constraint
--  set used in the member types.
data AnnBodyType c
  = AnnBodyType [AnnMemType c] [AnnMemType c]
      -- ^Constructs an annotation body type.  The arguments are the members of
      --  the annotation: lifted attributes first, schema attributes second.
  deriving (Eq, Ord, Show)

-- |An alias for normal annotation body types.
type NormalAnnBodyType = AnnBodyType ConstraintSet

instance (Pretty c) => Pretty (AnnBodyType c) where
  prettyLines (AnnBodyType ms1 ms2) =
    ["〈 "] %+ prettyLines ms1 %$ [", "] %+ prettyLines ms2 +% [" 〉"]

-- |Annotation member types.  The type parameter dictates the type of constraint
--  set that this member type uses.
data AnnMemType c = AnnMemType Identifier TPolarity MorphismArity QVar c
  deriving (Eq, Ord, Show)

-- |An alias for normal annotation member types.
type NormalAnnMemType = AnnMemType ConstraintSet

instance (Pretty c) => Pretty [AnnMemType c] where
  prettyLines ms = intersperseBoxes [", "] $ map prettyLines ms

instance (Pretty c) => Pretty (AnnMemType c) where
  prettyLines (AnnMemType i pol arity qa cs) =
    [i ++ " "] %+ prettyLines pol %+ prettyLines arity %+ [": "] %+
      prettyLines qa %+ ["\\"] %+ prettyLines cs

-- |A type to describe arities of morphisms in annotation member types.
data MorphismArity = PolyArity | MonoArity
  deriving (Eq, Ord, Show)

instance Pretty MorphismArity where
  prettyLines PolyArity = ["A"]
  prettyLines MonoArity = ["1"]

-- |A wrapper type for opaque type IDs.
newtype OpaqueID = OpaqueID Int
  deriving (Eq, Ord, Show)

-- |A data type describing the origins of opaque variables.
data OpaqueOrigin
  = OpaqueSourceOrigin UID
      -- ^Opaque variable produced directly from a type expression in source.
  | OpaqueAnnotationOrigin UID
      -- ^The opaque variable was constructed as part of typechecking an
      --  annotation.
  deriving (Eq, Ord, Show)

-- |A data type for opaque variables; these act as concrete types and are used
--  for declared polymorphism.
data OpaqueVar = OpaqueVar OpaqueOrigin OpaqueID
  deriving (Eq, Ord, Show)

instance Pretty OpaqueVar where
  prettyLines (OpaqueVar _ (OpaqueID n)) = ["α*" ++ show n]
  
-- |Shallow types
data ShallowType
  = SFunction UVar UVar
  | STrigger UVar
  | SBool
  | SInt
  | SReal
  | SString
  | SOption QVar
  | SIndirection QVar
  | STuple [QVar]
  | SRecord (Map Identifier QVar) (Set OpaqueVar)
  | STop
  | SBottom
  | SOpaque OpaqueVar
  deriving (Eq, Ord, Show)
  
instance Pretty ShallowType where
  prettyLines t = case t of
    SFunction a a' -> prettyLines a %+ ["->"] %+ prettyLines a'
    STrigger a' -> ["trigger "] %+ prettyLines a'
    SBool -> ["bool"]
    SInt -> ["int"]
    SReal -> ["real"]
    SString -> ["string"]
    SOption qa -> ["option "] %+ prettyLines qa
    SIndirection qa -> ["ind "] %+ prettyLines qa
    STuple qas -> ["("] %+ intersperseBoxes [","] (map prettyLines qas) %+ [")"]
    SRecord rows oas ->
      let rowBox (i,qa) = [i++":"] %+ prettyLines qa in
      ["{"] %+ intersperseBoxes [","] (map rowBox $ sort $ Map.toList rows) +%
      ["}"] %+
      if Set.null oas then [] else
        ["&{"] %+ intersperseBoxes [","] (map prettyLines $ sort $
                                            Set.toList oas) +% ["}"]
    STop -> ["⊤"]
    SBottom -> ["⊥"]
    SOpaque ao -> prettyLines ao

-- |A simple data type for polarities.  Polarities are monoidal by XOR.  The
--  empty polarity is positive.
data TPolarity = Positive | Negative
  deriving (Eq, Ord, Read, Show)

instance Pretty TPolarity where
  prettyLines pol = case pol of
                      Positive -> ["+"]
                      Negative -> ["-"]

instance Monoid TPolarity where
  mempty = Positive
  mappend x y = if x == y then Positive else Negative

-- |Type environments.
type TEnv a = Map TEnvId a

-- |Type environment identifiers.
data TEnvId
  = TEnvIdentifier Identifier
  | TEnvIdContent
  | TEnvIdHorizon
  | TEnvIdFinal
  | TEnvIdSelf
  deriving (Eq, Ord, Read, Show)

instance Pretty TEnvId where
  prettyLines i = case i of
    TEnvIdentifier i' -> [i']
    TEnvIdContent -> ["content"]
    TEnvIdHorizon -> ["horizon"]
    TEnvIdFinal -> ["structure"]
    TEnvIdSelf -> ["self"]

-- |Type alias environment entries.  The type parameter is passed to the
--  underlying quantified and annotation types.
data TypeAliasEntry c = QuantAlias (QuantType c) | AnnAlias (AnnType c)
  deriving (Eq, Show)

instance (Pretty c) => Pretty (TypeAliasEntry c) where
  prettyLines tae = case tae of
    QuantAlias qt -> prettyLines qt
    AnnAlias ann -> prettyLines ann
  
-- |A type alias for normal alias entries (those which use normal constraint
--  sets).
type NormalTypeAliasEntry = TypeAliasEntry ConstraintSet

-- |A type alias for the kind of polymorphism information stored in a QuantEnv.
type TQuantEnvValue c = (UVar, TypeOrVar, TypeOrVar, c)

-- |An alias for type alias environments.
type TAliasEnv = TEnv NormalTypeAliasEntry
-- |An alias for normal type environments.
type TNormEnv = TEnv NormalQuantType
-- |An alias for type parameter environments.
type TParamEnv = TEnv UVar
-- |An alias for quantified (polymorphism) environments.
type TQuantEnv = TEnv (TQuantEnvValue ConstraintSet)
-- |An alias for global quantified (polymorphism) environments.
type TGlobalQuantEnv = TEnv TQuantEnv

-- |A type alias describing a type or a variable.
type TypeOrVar = Coproduct ShallowType UVar
-- |A type alias describing a type qualifier or qualified variable.
type QualOrVar = Coproduct (Set TQual) QVar
-- |A type alias describing a type or any kind of variable.
type UVarBound = Coproduct TypeOrVar QVar

-- * Constraints

-- |A data type to describe constraints.
data Constraint
  = IntermediateConstraint TypeOrVar TypeOrVar
  | QualifiedLowerConstraint TypeOrVar QVar
  | QualifiedUpperConstraint QVar TypeOrVar
  | QualifiedIntermediateConstraint QualOrVar QualOrVar
  | BinaryOperatorConstraint UVar BinaryOperator UVar UVar
  -- TODO: unary prefix operator constraint?  it's not in the spec, but the
  --       implementation parses "!"
  | MonomorphicQualifiedUpperConstraint QVar (Set TQual)
  | PolyinstantiationLineageConstraint QVar QVar
  | OpaqueBoundConstraint OpaqueVar TypeOrVar TypeOrVar
  deriving (Eq, Ord, Show)
  
instance Pretty Constraint where
  prettyLines c =
    case c of
      IntermediateConstraint ta1 ta2 -> binPretty ta1 ta2
      QualifiedLowerConstraint ta qa -> binPretty ta qa
      QualifiedUpperConstraint qa ta -> binPretty qa ta
      QualifiedIntermediateConstraint qv1 qv2 -> binPretty qv1 qv2
      BinaryOperatorConstraint a1 op a2 a3 ->
        prettyLines a1 %+ prettyLines op %+ prettyLines a2 %+ ["<:"] %+
        prettyLines a3
      MonomorphicQualifiedUpperConstraint qa qs ->
        prettyLines qa %+ ["<:"] %+ prettyLines qs
      PolyinstantiationLineageConstraint qa1 qa2 ->
        prettyLines qa1 %+ ["<<:"] %+ prettyLines qa2
      OpaqueBoundConstraint oa lb ub ->
        ["("] %+ prettyLines lb %+ ["≤"] %+ prettyLines oa %+ ["≤"] %+
          prettyLines ub %+ [")"]
    where
      binPretty x y = prettyLines x %+ ["<:"] %+ prettyLines y
  
-- |A data type representing binary operators in the type system.
data BinaryOperator
  = BinOpAdd
  | BinOpSubtract
  | BinOpMultiply
  | BinOpDivide
  | BinOpEquals
  | BinOpGreater
  | BinOpLess
  | BinOpGreaterEq
  | BinOpLessEq
  | BinOpSequence
  | BinOpApply
  | BinOpSend
  deriving (Eq, Ord, Read, Show)
  
instance Pretty BinaryOperator where
  prettyLines op = (case op of
      BinOpAdd -> "+"
      BinOpSubtract -> "-"
      BinOpMultiply -> "*"
      BinOpDivide -> "/"
      BinOpEquals -> "=="
      BinOpGreater -> ">"
      BinOpLess -> "<"
      BinOpGreaterEq -> ">="
      BinOpLessEq -> "<="
      BinOpSequence -> ";"
      BinOpApply -> ""
      BinOpSend -> "<-"
    ):[]
  
-- |A data type representing some form of operator.
data AnyOperator
  = SomeBinaryOperator BinaryOperator
  deriving (Eq, Ord, Read, Show)
  
-- * Constraint sets

-- |A data type for sets of constraints.  This data type is not a type alias
--  to help ensure that it is treated abstractly by its users.  This will
--  permit structural changes for performance optimization in the future.
data ConstraintSet = ConstraintSet (Set Constraint)
  deriving (Eq, Ord, Show)
  
instance Monoid ConstraintSet where
  mempty = ConstraintSet Set.empty
  mappend (ConstraintSet cs1) (ConstraintSet cs2) =
    ConstraintSet $ Set.union cs1 cs2

instance Pretty ConstraintSet where
  prettyLines (ConstraintSet cs) =
    -- Filter out self-constraints.
    let filteredCs = filter (not . silly) $ Set.toList cs in
    ["{ "] %+
    (sequenceBoxes (max 1 $ maxWidth - 4) ", " $ map prettyLines filteredCs) +%
    [" }"] +%
      if Set.size cs /= length filteredCs then ["*"] else []
    where
      silly :: Constraint -> Bool
      silly c = case c of
        IntermediateConstraint x y -> x == y
        QualifiedIntermediateConstraint x y -> x == y
        _ -> False
