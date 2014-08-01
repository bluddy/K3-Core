{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- | Data types for Hindley-Milner inference.
--   We use a separate tree data type to ensure no mixing of type systems.
module Language.K3.Analysis.HMTypes.DataTypes where

import Data.List
import Data.Tree
import Data.Set

import Language.K3.Core.Annotation
import Language.K3.Core.Common
import Language.K3.Utils.Pretty

type QTVarId = Int

-- Polymorphic type
-- 1. All polymorphic vars in the type
-- 2. Type
data QPType = QPType [QTVarId] (K3 QType)
                deriving (Eq, Read, Show)

data QType
        = QTBottom
        -- QTOpen children:
        -- 1. lower bound (lowest supertype that must be supported)
        -- 2. upper bound (highest subtype that must be supported)
        -- Any missing bounds are replaced with QTBottom
        | QTOpen
        | QTPrimitive QTBase
        | QTConst     QTData
        | QTVar       QTVarId
        | QTContent
        | QTFinal
          -- Self type is a recursive collection type.
        | QTSelf
        | QTTop
      deriving (Eq, Read, Show)

-- | Primitive types.
--   Note this class derives an enum instance which we use to determine precedence.
--   Hence the ordering of the constructors should not be changed lightly.
data QTBase
        = QTBool
        | QTByte
        | QTReal
        | QTInt
        | QTString
        | QTAddress
        | QTNumber
      deriving (Eq, Read, Show)

qtEnumOfBase :: QTBase -> Int
qtEnumOfBase QTBool    = 0
qtEnumOfBase QTByte    = 1
qtEnumOfBase QTReal    = 2
qtEnumOfBase QTInt     = 3
qtEnumOfBase QTString  = 4
qtEnumOfBase QTAddress = 5
qtEnumOfBase QTNumber  = 6

qtBaseOfEnum :: QTBase -> Int
qtBaseOfEnum 0 = QTBool
qtBaseOfEnum 1 = QTByte
qtBaseOfEnum 2 = QTReal
qtBaseOfEnum 3 = QTInt
qtBaseOfEnum 4 = QTString
qtBaseOfEnum 5 = QTAddress
qtBaseOfEnum 6 = QTNumber

data QTData
        = QTFunction
        | QTOption
        | QTIndirection
        | QTTuple
        | QTRecord [Identifier]
        | QTCollection [Identifier]
          -- child is element type
        | QTTrigger
        | QTSource
        | QTSink
      deriving (Read, Show)

-- Make records and collections equal independent of id order
instance Eq QTData where
  QTFunction         == QTFunction          = True
  QTOption           == QTOption            = True
  QTIndirection      == QTIndirection       = True
  QTTuple            == QTTuple             = True
  (QTRecord ids)     == (QTRecord ids')     = HashSet.fromList ids == HashSet.fromList ids'
  (QTCollection ids) == (QTCollection ids') = HashSet.fromList ids == HashSet.fromList ids'
  QTTrigger          == QTTrigger           = True
  QTSource           == QTSource            = True
  QTSink             == QTSink              = True
  _                  == _                   = False

-- | Annotations on types are the mutability qualifiers.
data instance Annotation QType
    = QTMutable
    | QTImmutable
    | QTUID UID
  deriving (Eq, Read, Show)

-- | Type constructors
tleaf :: QType -> K3 QType
tleaf t = Node (t :@: []) []

tdata :: QTData -> [K3 QType] -> K3 QType
tdata d c = Node (QTConst d :@: []) c

tprim :: QTBase -> K3 QType
tprim b = tleaf $ QTPrimitive b

tvar :: QTVarId -> K3 QType
tvar i = Node (QTVar i :@: []) []

ttop :: K3 QType
ttop = tleaf QTTop

tbot :: K3 QType
tbot = tleaf QTBottom

tcontent :: K3 QType
tcontent = tleaf QTContent

tfinal :: K3 QType
tfinal = tleaf QTFinal

tself :: K3 QType
tself = tleaf QTSelf


-- | Datatype constructors
tfun :: K3 QType -> K3 QType -> K3 QType
tfun arg ret = tdata QTFunction [arg, ret]

topt :: K3 QType -> K3 QType
topt c = tdata QTOption [c]

tind :: K3 QType -> K3 QType
tind c = tdata QTIndirection [c]

ttup :: [K3 QType] -> K3 QType
ttup c = tdata QTTuple c

trec :: [(Identifier, K3 QType)] -> K3 QType
trec idt =
  let (ids, ts) = unzip idt in
  Node (QTRecord ids) ts

topen :: K3 QType -> K3 QType -> K3 Qtype
topen low high = Node QTOpen [low, high]

tcol :: K3 QType -> [Identifier] -> K3 QType
tcol ct annIds = tdata (QTCollection annIds) [ct]

ttrg :: K3 QType -> K3 QType
ttrg t = tdata QTTrigger [t]

tsrc :: K3 QType -> K3 QType
tsrc t = tdata QTSource [t]

tsnk :: K3 QType -> K3 QType
tsnk t = tdata QTSink [t]


-- | Primitive type constructors

tbool :: K3 QType
tbool = tprim QTBool

tbyte :: K3 QType
tbyte = tprim QTByte

tint :: K3 QType
tint = tprim QTInt

treal :: K3 QType
treal = tprim QTReal

tstr :: K3 QType
tstr = tprim QTString

taddr :: K3 QType
taddr = tprim QTAddress

tnum :: K3 QType
tnum = tprim QTNumber

tunit :: K3 QType
tunit = ttup []

-- | Annotation predicates
isQTQualified :: Annotation QType -> Bool
isQTQualified QTImmutable = True
isQTQualified QTMutable   = True
isQTQualified _ = False

isQTUID :: Annotation QType -> Bool
isQTUID (QTUID _) = True
isQTUID _ = False

isQTNumeric :: K3 QType -> Bool
isQTNumeric (tag -> QTPrimitive QTInt)    = True
isQTNumeric (tag -> QTPrimitive QTReal)   = True
isQTNumeric (tag -> QTPrimitive QTNumber) = True
isQTNumeric (Node QTOpen [QTBottom, t])   = isQTNumeric t
isQTNumeric (Node QTOpen [t,_])           = isQTNumeric t
isQTNumeric _ = False

getQTNumeric (tag -> QTPrimitive QTInt)    = Just QTInt
getQTNumeric (tag -> QTPrimitive QTReal)   = Just QTReal
getQTNumeric (tag -> QTPrimitive QTNumber) = Just QTNumber
getQTNumeric (Node QTOpen [QTBottom, t])  = getQTNumeric t
getQTNumeric _ = Nothing

isQTVar :: K3 QType -> Bool
isQTVar (tag -> QTVar _) = True
isQTVar _ = False

isQTOpen:: K3 QType -> Bool
isQTOpen (tag -> QTOpen) = True
isQTOpen _ = False

isQTClosed :: K3 QType -> Bool
isQTClosed = not . isQTOpen

isQTBottom :: K3 QType -> Bool
isQTBottom (Node QTBottom _) = True
isQTBottom _ = False

isQTRecord :: K3 QType -> Bool
isQTRecord (tag -> QTConst (QTRecord _))          = True
isQTRecord (Node QTOpen [isQTBottom -> True, t])  = isQTRecord t
isQTRecord (Node QTOpen [t, _])                   = isQTRecord t
isQTRecord _ = False

isQTCollection :: K3 QType -> Bool
isQTCollection (tag -> QTConst (QTCollection _)) = True
isQTCollection (Node QTOpen [isQTBottom -> True, t])  = isQTCollection t
isQTCollection (Node QTOpen [t, _])                   = isQTCollection t
isQTCollection _ = False

getQTRecordIds :: K3 QType -> Maybe [Identifier]

getQTUID :: Annotation QType -> UID
getQTUID (QTUID uid) = uid
getQTUID _ = -1

instance Pretty QTVarId where
  prettyLines x = [show x]

instance Pretty QTBase where
  prettyLines x = [show x]

instance Pretty QTData where
  prettyLines x = [show x]

instance Pretty (K3 QType) where
  prettyLines (Node (t :@: as) ts) = (show t ++ drawAnnotations as) : drawSubTrees ts

instance Pretty QPType where
  prettyLines (QPType tvars qt) = [unwords ["QPT", show tvars] ++ " "] %+ (prettyLines qt)
