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

data QPType = QPType (Set QTVarId) (K3 QType)
                deriving (Eq, Ord, Read, Show)

data QType
        = QTBottom
        | QTPrimitive QTOpen QTBase 
        | QTConst     QTData
        | QTVar       QTVarId
        | QTContent
        | QTFinal
        | QTSelf
        | QTTop
      deriving (Eq, Ord, Read, Show)

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
      deriving (Enum, Eq, Ord, Read, Show)

data QTContra = QTCovariant | QTContravariant
data QTOpen = QTClosed | QTOpen QTContra

data QTData
        = QTFunction
        | QTOption
        | QTIndirection
        | QTTuple
        | QTRecord QTOpen [Identifier]
        | QTCollection [Identifier]
        | QTTrigger
        | QTSource
        | QTSink
      deriving (Eq, Ord, Read, Show)

-- | Annotations on types are the mutability qualifiers.
data instance Annotation QType
    = QTMutable
    | QTImmutable
    | QTUID UID
  deriving (Eq, Ord, Read, Show)

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

trec :: QTOpen -> [(Identifier, K3 QType)] -> K3 QType
trec open idt =
  let (ids, ts) = unzip idt in
  tdata (QTRecord open ids) ts

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
isQTNumeric (tag -> QTPrimitive _ QTInt)    = True
isQTNumeric (tag -> QTPrimitive _ QTReal)   = True
isQTNumeric (tag -> QTPrimitive _ QTNumber) = True
isQTNumeric _ = False

isQTVar :: K3 QType -> Bool
isQTVar (tag -> QTVar _) = True
isQTVar _ = False

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
