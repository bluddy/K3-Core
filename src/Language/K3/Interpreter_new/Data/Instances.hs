{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Language.K3.Interpreter_new.Data.Instances where

import qualified Data.Map as Map

import Data.Hashable
import Data.Map ( Map )
import System.Mem.StableName
import Text.Read hiding ( get, lift )

import Language.K3.Core.Common
import Language.K3.Interpreter_new.Data.Types
import Language.K3.Runtime.FileDataspace
import Language.K3.Utils.Pretty

{- Value equality -}

-- | Haskell Eq type class implementation.
--   This uses entity-tag equality for indirections, functions and triggers.
--   All other values use structural equality.
instance Eq Value where
  VBool v             == VBool v'             = v == v'
  VByte v             == VByte v'             = v == v'
  VInt  v             == VInt  v'             = v == v'
  VReal v             == VReal v'             = v == v'
  VString v           == VString v'           = v == v'
  VAddress v          == VAddress v'          = v == v'  
  VOption v           == VOption v'           = v == v'
  VTuple v            == VTuple v'            = v == v'
  VRecord v           == VRecord v'           = v == v'   -- Equality based on Data.Map.Eq
  VIndirection (_,tg) == VIndirection (_,tg') = tg == tg'  
  VFunction (_,_,tg)  == VFunction (_,_,tg')  = tg == tg'
  VTrigger (n,_,tg)   == VTrigger (n',_,tg')  = n == n' && tg == tg'
  
  -- Collections must compare their namespaces due to mutable members.
  VCollection (_,v)   == VCollection (_,v') =
    (realizationId v, namespace v, dataspace v)
      == (realizationId v', namespace v', dataspace v')

  _                   == _                    = False

instance Eq EntityTag where
  (MemEntTag s1) == (MemEntTag s2) = hashStableName s1 == hashStableName s2
  (ExtEntTag i)  == (ExtEntTag j)  = i == j
  _ == _ = False

instance (Eq a) => Eq (CollectionNamespace a) where
  (CollectionNamespace cns ans) == (CollectionNamespace cns' ans') =
    cns == cns' && ans == ans'

-- | Eq typeclass instance for dataspaces.
--   This does not support equality for external dataspaces, due to purity constraints.
--   The interpreter must provide its own method for equality guarding against external dataspaces.
instance (Eq a) => Eq (CollectionDataspace a) where
  (InMemoryDS l)    == (InMemoryDS l')   = l == l'
  (InMemDS primDS)  == (InMemDS primDS') = primDS == primDS'
  _                 == _                 = error "Incomparable dataspaces"


-- | Eq instance declaration for list-based primitive in-memory dataspaces.
deriving instance (Eq a) => Eq (PrimitiveMDS a)
deriving instance (Eq a) => Eq (ListMDS a)
deriving instance (Eq a) => Eq (SetAsOrdListMDS a)
deriving instance (Eq a) => Eq (BagAsOrdListMDS a)

-- | Eq typeclass instance for environment entries.
deriving instance Eq (IEnvEntry Value)
deriving instance Eq ProxyStep

-- | Haskell Ord type class implementation.
--   Comparisons for indirections, functions and triggers use hash ordering.
instance Ord Value where
  compare (VBool a)    (VBool b)    = compare a b
  compare (VByte a)    (VByte b)    = compare a b
  compare (VInt a)     (VInt b)     = compare a b
  compare (VReal a)    (VReal b)    = compare a b
  compare (VString a)  (VString b)  = compare a b
  compare (VAddress a) (VAddress b) = compare a b
  compare (VOption a)  (VOption b)  = compare a b
  compare (VTuple a)   (VTuple b)   = compare a b
  compare (VRecord a)  (VRecord b)  = compare a b    -- Based on Data.Map.Ord

  compare (VIndirection (_,tga)) (VIndirection (_,tgb)) = compare tga tgb
  compare (VFunction (_,_,tga))  (VFunction (_,_,tgb))  = compare tga tgb
  compare (VTrigger (n,_,tga))   (VTrigger (n',_,tgb))  = compare (n,tga) (n',tgb)

  compare (VCollection (_,v)) (VCollection (_,v')) =
    compare (realizationId v, namespace v, dataspace v)
            (realizationId v', namespace v', dataspace v')

  compare _ _ = error "Invalid value comparison"

instance Ord EntityTag where
  compare (MemEntTag s1) (MemEntTag s2) = compare (hashStableName s1) (hashStableName s2)
  compare (ExtEntTag i)  (ExtEntTag j)  = compare i j
  compare (MemEntTag _)  (ExtEntTag _)  = LT
  compare (ExtEntTag _)  (MemEntTag _)  = GT

instance (Ord a) => Ord (CollectionNamespace a) where
  compare (CollectionNamespace cns ans) (CollectionNamespace cns' ans') =
    compare (cns, ans) (cns', ans')

-- | Ord typeclass instance for dataspaces.
--   Much like Eq, this does not support comparison of external dataspaces.
--   The interpreter must provide its own method guarding against external dataspaces.
instance (Ord a) => Ord (CollectionDataspace a) where
  compare (InMemoryDS l)   (InMemoryDS l')   = compare l l'
  compare (InMemDS primDS) (InMemDS primDS') = compare primDS primDS'
  compare _                _                 = error "Incomparable dataspaces"

-- | Ord instance declaration for list-based primitive in-memory dataspaces.
deriving instance (Ord a) => Ord (PrimitiveMDS a)
deriving instance (Ord a) => Ord (ListMDS a)
deriving instance (Ord a) => Ord (SetAsOrdListMDS a)
deriving instance (Ord a) => Ord (BagAsOrdListMDS a)

-- | Haskell Hashable type class implementation.
--   Indirections, functions and triggers return the hash code of their entity tag.
instance Hashable Value where
  hashWithSalt salt (VBool a)           = hashWithSalt salt a
  hashWithSalt salt (VByte a)           = hashWithSalt salt a
  hashWithSalt salt (VInt a)            = hashWithSalt salt a
  hashWithSalt salt (VReal a)           = hashWithSalt salt a
  hashWithSalt salt (VString a)         = hashWithSalt salt a
  hashWithSalt salt (VAddress a)        = hashWithSalt salt a
  hashWithSalt salt (VOption a)         = hashWithSalt salt a
  hashWithSalt salt (VTuple a)          = hashWithSalt salt a
  hashWithSalt salt (VRecord a)         = hashWithSalt salt a

  hashWithSalt salt (VIndirection (_,tg)) = hashWithSalt salt tg
  hashWithSalt salt (VFunction (_,_,tg))  = hashWithSalt salt tg
  hashWithSalt salt (VTrigger (_,_,tg))   = hashWithSalt salt tg

  hashWithSalt salt (VCollection (_,a)) =
    salt `hashWithSalt` (namespace a) `hashWithSalt` (dataspace a) 

instance Hashable MemberQualifier

instance Hashable EntityTag where
  hashWithSalt salt (MemEntTag sn) = salt `hashWithSalt` (hashStableName sn)
  hashWithSalt salt (ExtEntTag i)  = salt `hashWithSalt` i

instance (Hashable a) => Hashable (NamedBindings a) where
  hashWithSalt salt nb = salt `hashWithSalt` (Map.foldl hashWithSalt 0 nb) 

instance (Hashable a) => Hashable (CollectionNamespace a) where
  hashWithSalt salt (CollectionNamespace cns ans) =
    salt `hashWithSalt` cns `hashWithSalt` ans

-- | Hashable instance for dataspaces. External dataspaces are not supported.
instance (Hashable a) => Hashable (CollectionDataspace a) where
  hashWithSalt salt (InMemoryDS l)   = salt `hashWithSalt` (0 :: Int) `hashWithSalt` l
  hashWithSalt salt (InMemDS primDS) = salt `hashWithSalt` (1 :: Int) `hashWithSalt` primDS
  hashWithSalt _ _                   = error "Unhashable dataspace"


-- | Hashable instance declaration for list-based primitive in-memory dataspaces.
instance (Hashable a) => Hashable (PrimitiveMDS a) where
  hashWithSalt salt (MemDS    l) = salt `hashWithSalt` (0 :: Int) `hashWithSalt` l 
  hashWithSalt salt (SeqDS    l) = salt `hashWithSalt` (1 :: Int) `hashWithSalt` l 
  hashWithSalt salt (SetDS    l) = salt `hashWithSalt` (2 :: Int) `hashWithSalt` l 
  hashWithSalt salt (SortedDS l) = salt `hashWithSalt` (3 :: Int) `hashWithSalt` l 

deriving instance (Hashable a) => Hashable (ListMDS a)
deriving instance (Hashable a) => Hashable (SetAsOrdListMDS a)
deriving instance (Hashable a) => Hashable (BagAsOrdListMDS a)



-- | Read and show instances for Interpreter datatypes.

showsPrecTag :: Show a => String -> Int -> a -> ShowS
showsPrecTag s d v = showsPrecTagF s d $ showsPrec (appPrec+1) v
  where appPrec = 10

showsPrecTagF :: String -> Int -> ShowS -> ShowS
showsPrecTagF s d showF =
  showParen (d > appPrec) $ showString (s++" ") . showF
  where appPrec = 10

-- | Verbose stringification of values through show instance.
--   This produces <tag> placeholders for unshowable values (IORefs and functions)
instance Show Value where
  showsPrec d (VBool v)            = showsPrecTag "VBool" d v
  showsPrec d (VByte v)            = showsPrecTag "VByte" d v
  showsPrec d (VInt v)             = showsPrecTag "VInt" d v
  showsPrec d (VReal v)            = showsPrecTag "VReal" d v
  showsPrec d (VString v)          = showsPrecTag "VString" d v
  showsPrec d (VOption v)          = showsPrecTag "VOption" d v
  showsPrec d (VTuple v)           = showsPrecTag "VTuple" d v
  showsPrec d (VRecord v)          = showsPrecTag "VRecord" d v
  showsPrec d (VAddress v)         = showsPrecTag "VAddress" d v  
  showsPrec d (VCollection (_,c))  = showsPrecTag "VCollection"  d c

  showsPrec d (VIndirection (_,tg))       = showsPrecTagF "VIndirection" d $ showString $ "<" ++ (show tg) ++ ">"
  showsPrec d (VFunction (_,_,tg))        = showsPrecTagF "VFunction"    d $ showString $ "<" ++ (show tg) ++ ">"
  showsPrec d (VTrigger (_, Nothing, tg)) = showsPrecTagF "VTrigger"     d $ showString $ "<uninitialized:" ++ (show tg) ++">"
  showsPrec d (VTrigger (_, Just _, tg))  = showsPrecTagF "VTrigger"     d $ showString $ "<function:" ++ (show tg) ++ ">"

instance Show EntityTag where
  showsPrec d (MemEntTag s) = showsPrecTag "MemEntTag" d (hashStableName s)
  showsPrec d (ExtEntTag i) = showsPrecTag "ExtEntTag" d i

deriving instance Show (Collection Value)
deriving instance Show (CollectionNamespace Value)
deriving instance Show (CollectionDataspace Value)
deriving instance Show (PrimitiveMDS Value)
deriving instance Show (ListMDS Value)
deriving instance Show (SetAsOrdListMDS Value)
deriving instance Show (BagAsOrdListMDS Value)

instance Show (AEnvironment Value) where
  showsPrec d (AEnvironment defs _) = showsPrecTag "AEnvironment" d defs

deriving instance Show ProxyStep

-- | Verbose stringification of values through read instance.
--   This errors on attempting to read unshowable values (IORefs and functions)
instance Read Value where
  readPrec = parens $ 
        (prec app_prec $ do
          Ident "VBool" <- lexP
          v <- step readPrec
          return (VBool v))

    +++ (prec app_prec $ do
          Ident "VByte" <- lexP
          v <- step readPrec
          return (VByte v))

    +++ (prec app_prec $ do
          Ident "VInt" <- lexP
          v <- step readPrec
          return (VInt v))

    +++ (prec app_prec $ do
          Ident "VReal" <- lexP
          v <- step readPrec
          return (VReal v))

    +++ (prec app_prec $ do
          Ident "VString" <- lexP
          v <- step readPrec
          return (VString v))

    +++ (prec app_prec $ do
          Ident "VOption" <- lexP
          v <- step readPrec
          return (VOption v))

    +++ (prec app_prec $ do
          Ident "VTuple" <- lexP
          v <- step readPrec
          return (VTuple v))

    +++ (prec app_prec $ do
          Ident "VRecord" <- lexP
          v <- step readPrec
          return (VRecord v))

    -- We cannot initialize the self pointer in pure fashion for collections
    +++ (prec app_prec $ do
          Ident "VCollection" <- lexP
          _ <- step (readPrec :: ReadPrec (Collection Value))
          error "Cannot read collections")

    +++ (prec app_prec $ do
          Ident "VIndirection" <- lexP
          Ident "<opaque>" <- step readPrec
          error "Cannot read indirections")

    +++ (prec app_prec $ do
          Ident "VFunction" <- lexP
          Ident "<function>" <- step readPrec
          error "Cannot read functions")

    +++ (prec app_prec $ do
          Ident "VAddress" <- lexP
          v <- step readPrec
          return (VAddress v))

    +++ (prec app_prec $ do
          Ident "VTrigger" <- lexP
          Ident _ <- lexP
          Ident "<uninitialized>" <- step readPrec
          error "Cannot read triggers")

    +++ (prec app_prec $ do
          Ident "VTrigger" <- lexP
          Ident _ <- lexP
          Ident "<function>" <- step readPrec
          error "Cannot read triggers")

    where app_prec = 10

  readListPrec = readListPrecDefault

instance Read EntityTag where
  readPrec = parens $ 
        (prec app_prec $ do
          Ident "MemEntTag" <- lexP
          _ <- step (readPrec :: ReadPrec Int)
          error "Cannot read in-memory entity tags")
          -- Above, we cannot obtain the original stable name corresponding to its hashed value.

    +++ (prec app_prec $ do
          Ident "ExtEntTag" <- lexP
          n <- step readPrec
          return $ ExtEntTag n)

    where app_prec = 10

deriving instance Read (Collection Value)
deriving instance Read (CollectionNamespace Value)
deriving instance Read (CollectionDataspace Value)
deriving instance Read (PrimitiveMDS Value)
deriving instance Read (ListMDS Value)
deriving instance Read (SetAsOrdListMDS Value)
deriving instance Read (BagAsOrdListMDS Value)

-- | Note this is a partial instance, since we rely on EntityTag.
deriving instance Read ProxyStep

-- | Pretty printing instances
prettyOption :: (Pretty a) => Maybe a -> [String]
prettyOption Nothing  = ["Nothing"]
prettyOption (Just a) = shift "Just" "  " $ prettyLines a

prettyMap :: (Pretty a) => Map Identifier a -> [String]
prettyMap m = concatMap (uncurry prettyEntry) mList
    where mList  = Map.toAscList m
          nWidth = maximum . map (length . fst) $ mList
          prettyEntry x y   = [(suffixPadTo nWidth x) ++ " => "] %+ prettyLines y
          suffixPadTo len n = n ++ replicate (max (len - length n) 0) ' '

prettyAssocList :: (Pretty a) => [(Identifier, a)] -> [String]
prettyAssocList l = concatMap (uncurry prettyEntry) l
    where nWidth            = maximum $ map (length . fst) l
          prettyEntry x y   = [(suffixPadTo nWidth x) ++ " => "] %+ prettyLines y
          suffixPadTo len n = n ++ replicate (max (len - length n) 0) ' '

instance Pretty Value where
  prettyLines v = [show v]

instance Pretty [Value] where
  prettyLines vl = concatMap prettyLines vl

instance Pretty EntityTag where
  prettyLines v = [show v]

instance Pretty MemberQualifier where
  prettyLines v = [show v]

instance Pretty (Value, MemberQualifier) where
  prettyLines (v,q) = shift (show q ++ " ") "  " $ prettyLines v

instance Pretty (NamedBindings Value) where
  prettyLines nb = prettyMap nb

instance Pretty (NamedMembers Value) where
  prettyLines nm = prettyMap nm

instance Pretty [(Identifier, NamedMembers Value)] where
  prettyLines = prettyAssocList

instance Pretty (Collection Value) where
  prettyLines (Collection ns ds cId) =
    ["Collection " ++ cId] ++ (indent 2 $ prettyLines ns) ++ (indent 2 $ prettyLines ds) 

instance Pretty (CollectionNamespace Value) where
  prettyLines (CollectionNamespace cns ans) =
    ["CollectionNamespace"] ++ (indent 2 $ prettyLines cns) ++ (indent 2 $ prettyLines ans)

instance Pretty (CollectionDataspace Value) where
  prettyLines (InMemoryDS l)    = ["InMemoryDS"] ++ (indent 2 $ prettyLines l)
  prettyLines (InMemDS primMDS) = ["InMemDS"] ++ (indent 2 $ prettyLines primMDS) 
  prettyLines (ExternalDS (FileDataspace fId)) = ["ExternalDS (FileDataspace " ++ fId ++ ")"]

instance Pretty (PrimitiveMDS Value) where
  prettyLines (MemDS    l) = ["MemDS"]    ++ (indent 2 $ prettyLines l)
  prettyLines (SeqDS    l) = ["SeqDS"]    ++ (indent 2 $ prettyLines l)
  prettyLines (SetDS    l) = ["SetDS"]    ++ (indent 2 $ prettyLines l)
  prettyLines (SortedDS l) = ["SortedDS"] ++ (indent 2 $ prettyLines l)

deriving instance Pretty (ListMDS Value)
deriving instance Pretty (SetAsOrdListMDS Value)
deriving instance Pretty (BagAsOrdListMDS Value)

instance Pretty (AEnvironment Value) where
  prettyLines (AEnvironment defs _) = ["AEnvironment"] ++ (indent 2 $ prettyLines defs)

instance Pretty ProxyStep where
  prettyLines (Named n)             = ["Named " ++ n]
  prettyLines (Temporary n)         = ["Temporary " ++ n]
  prettyLines (Dataspace (n,tg))    = ["Dataspace (" ++ n ++ "," ++ show tg++ ")"]
  prettyLines  ProxySelf            = ["ProxySelf"]
  prettyLines  Dereference          = ["Dereference"]
  prettyLines  MatchOption          = ["MatchOption"]
  prettyLines (TupleField i)        = ["TupleField " ++ show i]
  prettyLines (RecordField n)       = ["RecordField " ++ show n]
  prettyLines (CollectionMember n)  = ["CollectionMember " ++ show n]

instance Pretty ProxyPath where
  prettyLines path = concatMap prettyLines path

instance Pretty ProxyPathStack where
  prettyLines pStack = concatMap prettyOption pStack 

instance Pretty InterpretationError where
  prettyLines err = [show err]

-- | Interpreter state and result printing instances.
--   These instances are partial; for complete output use L.K3.I.Utils.prettyI{State|Result}M
instance Pretty IState where
  prettyLines istate =
         ["Environment:"] ++ ["<opaque>"] --(indent 2 $ map prettyEnvEntry $ Map.toAscList (getEnv istate))
      ++ ["Annotations:"] ++ (indent 2 $ lines $ show $ getAnnotEnv istate)
      ++ ["Static:"]      ++ (indent 2 $ lines $ show $ getStaticEnv istate)
      ++ ["Aliases:"]     ++ (indent 2 $ lines $ show $ getProxyStack istate)
    where
      prettyEnvEntry (n,v) = n ++ replicate (maxNameLength - length n) ' ' ++ " => " ++ show v
      maxNameLength        = 0 --maximum $ map (length . fst) $ Map.toAscList $ getEnv istate

instance (Pretty a) => Pretty (IResult a) where
  prettyLines ((r, st), _) = ["Status: "] ++ either ((:[]) . show) prettyLines r ++ prettyLines st

instance (Pretty a) => Pretty [(Address, IResult a)] where
  prettyLines l = concatMap (\(x,y) -> [""] ++ prettyLines x ++ (indent 2 $ prettyLines y)) l