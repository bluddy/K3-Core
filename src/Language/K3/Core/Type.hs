{-# LANGUAGE TypeFamilies #-}

-- | Types in K3.
module Language.K3.Core.Type
( Type(..)
, Annotation(..)
) where

import Language.K3.Core.Annotation
import Language.K3.Core.Common

-- * Basic types

-- | Tags in the Type Tree. Every type can be qualified with a mutability
--   annotation.  This set of tags is a superset of those which can be parsed
--   by the type expression grammar (spec sec 1.2) because it also represents
--   the (unparseable) types inferred by the type system.
data Type
    = TBool
    | TByte
    | TInt
    | TReal
    | TString
    | TOption
    | TIndirection
    | TTuple
    | TRecord [Identifier]
    | TCollection
    | TFunction
    | TAddress
    | TSource
    | TSink
    | TTrigger [Identifier]
  deriving (Eq, Read, Show)

-- | Annotations on types are the mutability qualifiers.
data instance Annotation Type
    = TMutable
    | TImmutable
    | TWitness
    | TSpan Span
    | TAnnotation Identifier
  deriving (Eq, Read, Show)

-- | TODO: pretty printing of type tree
