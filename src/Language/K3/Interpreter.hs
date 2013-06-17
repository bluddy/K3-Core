{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- | The K3 Interpreter
module Language.K3.Interpreter (
  -- | Types
  Value(..),

  Interpretation,
  InterpretationError,

  IEnvironment,
  ILog,

  -- | Interpreters
  runInterpretation,

  expression,
  program,
  runProgram
) where

import Control.Arrow

import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Writer

import Data.Function
import Data.IORef
import Data.List
import Data.Tree
import Data.Word (Word8)
import Debug.Trace

import Language.K3.Core.Annotation
import Language.K3.Core.Type
import Language.K3.Core.Expression
import Language.K3.Core.Declaration

import Language.K3.Pretty

-- | K3 Values
data Value
    = VBool        Bool
    | VByte        Word8
    | VInt         Int
    | VReal        Double
    | VString      String
    | VOption      (Maybe Value)
    | VTuple       [Value]
    | VRecord      [(Identifier, Value)]
    | VCollection  [Value]
    | VIndirection (IORef Value)
    | VFunction    (Value -> Interpretation Value)
    | VAddress     (String, Int)

-- We can't deriving Show because IORefs aren't showable.
instance Show Value where
  show (VBool b) = "VBool " ++ show b
  show (VByte b) = "VByte " ++ show b
  show (VInt i) = "VInt " ++ show i
  show (VReal r) = "VReal " ++ show r
  show (VString s) = "VString " ++ show s
  show (VOption m) = "VOption " ++ show m
  show (VTuple t) = "VTuple " ++ show t
  show (VRecord r) = "VRecord " ++ show r
  show (VCollection c) = "VCollection " ++ show c
  show (VIndirection _) = "VIndirection <opaque>"
  show (VFunction _) = "VFunction <function>"
  show (VAddress (host, port)) = "VAddress " ++ host ++ ":" ++ show port

-- | Interpretation event log.
type ILog = [String]

-- | Interpretation Environment.
type IEnvironment = [(Identifier, Value)]

-- | Errors encountered during interpretation.
data InterpretationError
    = RunTimeInterpretationError String
    | RunTimeTypeError String
  deriving (Eq, Read, Show)

-- | Pairing of errors and environments for debugging output.
type EnvOnError = (InterpretationError, IEnvironment)

-- | The Interpretation Monad. Computes a result (valid/error), with the final state and an event log.
type Interpretation = EitherT InterpretationError (StateT IEnvironment (WriterT ILog IO))

-- | Run an interpretation to get a value or error, resulting environment and event log.
runInterpretation :: IEnvironment -> Interpretation a -> IO ((Either InterpretationError a, IEnvironment), ILog)
runInterpretation e = runWriterT . flip runStateT e . runEitherT

-- | Interpret a K3 value and extract the resulting environment
envOfInterpretation :: IEnvironment -> Interpretation a -> IO (Either EnvOnError IEnvironment)
envOfInterpretation initEnv i = runInterpretation initEnv i >>= \case
                                  ((Right _, env), _) -> return $ Right env
                                  ((Left err, env), _) -> return $ Left (err, env)

-- | Raise an error inside an interpretation. The error will be captured alongside the event log
-- till date, and the current state.
throwE :: InterpretationError -> Interpretation a
throwE = Control.Monad.Trans.Either.left

-- | Look-up the environment, with a thrown error if unsuccessful.
lookupE :: Identifier -> Interpretation Value
lookupE n = get >>= maybe (throwE $ RunTimeTypeError $ "Unknown Variable: '" ++ n ++ "'") return . lookup n

children :: Tree a -> Forest a
children = subForest

{- Names -}
myAddrId = "me"

-- | Default values for specific types
defaultValue :: K3 Type -> Interpretation Value
defaultValue (tag -> TBool)       = return $ VBool False
defaultValue (tag -> TByte)       = return $ VByte 0
defaultValue (tag -> TInt)        = return $ VInt 0
defaultValue (tag -> TReal)       = return $ VReal 0.0
defaultValue (tag -> TString)     = return $ VString ""
defaultValue (tag -> TOption)     = return $ VOption Nothing
defaultValue (tag -> TCollection) = return $ VCollection []
defaultValue (tag -> TAddress)    = return $ VAddress ("localhost", 10000)

defaultValue (tag &&& children -> (TIndirection, [x])) = defaultValue x >>= liftIO . newIORef >>= return . VIndirection
defaultValue (tag &&& children -> (TTuple, ch))       = mapM defaultValue ch >>= return . VTuple
defaultValue (tag &&& children -> (TRecord ids, ch))  = mapM defaultValue ch >>= return . VRecord . zip ids
defaultValue _ = undefined


-- | Interpretation of Constants.
constant :: Constant -> Interpretation Value
constant (CBool b)   = return $ VBool b
constant (CInt i)    = return $ VInt i
constant (CByte w)   = return $ VByte w
constant (CReal r)   = return $ VReal r
constant (CString s) = return $ VString s
constant CNone       = return $ VOption Nothing
constant CEmpty      = return $ VCollection []

-- | Common Numeric-Operation handling, with casing for int/real promotion.
numeric :: (forall a. Num a => a -> a -> a) -> K3 Expression -> K3 Expression -> Interpretation Value
numeric op a b = do
  a' <- expression a
  b' <- expression b
  case (a', b') of
      (VInt x, VInt y) -> return $ VInt $ op x y
      (VInt x, VReal y) -> return $ VReal $ op (fromIntegral x) y
      (VReal x, VInt y) -> return $ VReal $ op x (fromIntegral y)
      (VReal x, VReal y) -> return $ VReal $ op x y
      _ -> throwE $ RunTimeTypeError "Arithmetic Type Mis-Match"

-- | Common boolean operation handling.
logic :: (Bool -> Bool -> Bool) -> K3 Expression -> K3 Expression -> Interpretation Value
logic op a b = do
  a' <- expression a
  b' <- expression b

  case (a', b') of
      (VBool x, VBool y) -> return $ VBool $ op x y
      _ -> throwE $ RunTimeTypeError "Invalid Boolean Operation"

-- | Common comparison operation handling.
comparison :: (forall a. Ord a => a -> a -> Bool) -> K3 Expression -> K3 Expression -> Interpretation Value
comparison op a b = do
  a' <- expression a
  b' <- expression b

  case (a', b') of
      (VBool x, VBool y) -> return $ VBool $ op x y
      (VInt x, VInt y) -> return $ VBool $ op x y
      (VReal x, VReal y) -> return $ VBool $ op x y
      (VString x, VString y) -> return $ VBool $ op x y
      _ -> throwE $ RunTimeTypeError "Comparison Type Mis-Match"

-- | Interpretation of unary operators.
unary :: Operator -> K3 Expression -> Interpretation Value

-- | Interpretation of unary negation of numbers.
unary ONeg a = expression a >>= \case
  VInt i -> return $ VInt (negate i)
  VReal r -> return $ VReal (negate r)
  _ -> throwE $ RunTimeTypeError "Invalid Negation"

-- | Interpretation of unary negation of booleans.
unary ONot a = expression a >>= \case
  VBool b -> return $ VBool (not b)
  _ -> throwE $ RunTimeTypeError "Invalid Complement"

unary _ _ = throwE $ RunTimeTypeError "Invalid Unary Operator"

-- | Interpretation of binary operators.
binary :: Operator -> K3 Expression -> K3 Expression -> Interpretation Value

-- | Standard numeric operators.
binary OAdd = numeric (+)
binary OSub = numeric subtract
binary OMul = numeric (*)

-- | Division handled similarly, but accounting zero-division errors.
binary ODiv = \a b -> do
  a' <- expression a
  b' <- expression b

  void $ case b' of
      VInt 0 -> throwE $ RunTimeInterpretationError "Division by Zero"
      VReal 0 -> throwE $ RunTimeInterpretationError "Division by Zero"
      _ -> return ()

  case (a', b') of
      (VInt x, VInt y) -> return $ VInt $ x `div` y
      (VInt x, VReal y) -> return $ VReal $ fromIntegral x / y
      (VReal x, VInt y) -> return $ VReal $ x / (fromIntegral y)
      (VReal x, VReal y) -> return $ VReal $ x / y
      _ -> throwE $ RunTimeTypeError "Arithmetic Type Mis-Match"

-- | Logical Operators
binary OAnd = logic (&&)
binary OOr  = logic (||)

-- | Comparison Operators
binary OEqu = comparison (==)
binary ONeq = comparison (/=)
binary OLth = comparison (<)
binary OLeq = comparison (<=)
binary OGth = comparison (>)
binary OGeq = comparison (>=)

-- | Function Application
binary OApp = \f x -> do
  f' <- expression f
  x' <- expression x

  case f' of
      VFunction b -> b x'
      _ -> throwE $ RunTimeTypeError "Invalid Function Application"

-- | Message Passing
binary OSnd = \target x -> do
  target' <- expression target
  x'      <- expression x
  env     <- get

  case (target', lookup myAddrId env) of 
    (VTuple [VFunction f', VAddress addr], Just (VAddress myAddr))
      | addr == myAddr -> f' x'
    (_, Nothing) -> throwE $ RunTimeTypeError "Invalid Local Address"
    _ -> throwE $ RunTimeTypeError "Invalid Trigger Target"

-- | Sequential expressions
binary OSeq = \e1 e2 -> expression e1 >> expression e2

binary _ = const . const $ throwE $ RunTimeInterpretationError "Unreachable"

-- | Interpretation of Expressions
expression :: K3 Expression -> Interpretation Value

-- | Interpretation of constant expressions.
expression (tag -> EConstant c) = constant c

-- | Interpretation of variable lookups.
expression (tag -> EVariable i) = lookupE i

-- | Interpretation of option type construction expressions.
expression (tag &&& children -> (ESome, [x])) = expression x >>= return . VOption . Just
expression (tag -> ESome) = throwE $ RunTimeTypeError "Invalid Construction of Option"

-- | Interpretation of indirection type construction expressions.
expression (tag &&& children -> (EIndirect, [x])) = expression x >>= liftIO . newIORef >>= return . VIndirection
expression (tag -> EIndirect) = throwE $ RunTimeTypeError "Invalid Construction of Indirection"

-- | Interpretation of tuple construction expressions.
expression (tag &&& children -> (ETuple, cs)) = mapM expression cs >>= return . VTuple

-- | Interpretation of record construction expressions.
expression (tag &&& children -> (ERecord is, cs)) = mapM expression cs >>= return . VRecord . zip is

-- | Interpretation of function construction.
expression (tag &&& children -> (ELambda i, [b])) = return $ VFunction $ \v -> modify ((i, v):) >> expression b

-- | Interpretation of unary/binary operators.
expression (tag &&& children -> (EOperate otag, cs))
    | otag `elem` [ONeg, ONot], [a] <- cs = unary otag a
    | otherwise, [a, b] <- cs = binary otag a b
    | otherwise = undefined

-- | Interpretation of Record Projection.
expression (tag &&& children -> (EProject i, [r])) = expression r >>= \case
    VRecord vr -> maybe (throwE $ RunTimeTypeError "Unknown Record Field") return $ lookup i vr
    _ -> throwE $ RunTimeTypeError "Invalid Record Projection"
expression (tag -> EProject _) = throwE $ RunTimeTypeError "Invalid Record Projection"

-- | Interpretation of Let-In Constructions.
expression (tag &&& children -> (ELetIn i, [e, b])) = expression e >>= modify . (:) . (i,) >> expression b
expression (tag -> ELetIn _) = throwE $ RunTimeTypeError "Invalid LetIn Construction"

-- | Interpretation of Assignment.
expression (tag &&& children -> (EAssign i, [e])) = lookupE i >>= \case
    VIndirection r -> expression e >>= liftIO . writeIORef r >> return (VTuple [])
    _ -> throwE $ RunTimeTypeError "Assignment to Non-Reference"
expression (tag -> EAssign _) = throwE $ RunTimeTypeError "Invalid Assignment"

-- | Interpretation of Case-Matches.
expression (tag &&& children -> (ECaseOf i, [e, s, n])) = expression e >>= \case
    VOption (Just v) -> modify ((i, v):) >> expression s
    VOption (Nothing) -> expression n
    _ -> throwE $ RunTimeTypeError "Invalid Argument to Case-Match"
expression (tag -> ECaseOf _) = throwE $ RunTimeTypeError "Invalid Case-Match"

-- | Interpretation of Binding.
expression (tag &&& children -> (EBindAs b, [e, f])) = expression e >>= \b' -> case (b, b') of
    (BIndirection i, VIndirection r) -> (modify . (:) $ (i, VIndirection r)) >> expression f
    (BTuple ts, VTuple vs) -> (modify . (++) $ zip ts vs) >> expression f
    (BRecord ids, VRecord ivs) -> do
        let (idls, idbs) = unzip $ sortBy (compare `on` fst) ids
        let (ivls, ivvs) = unzip $ sortBy (compare `on` fst) ivs
        if idls == ivls
            then modify ((++) (zip idbs ivvs)) >> expression f
            else throwE $ RunTimeTypeError "Invalid Bind-Pattern"
    _ -> throwE $ RunTimeTypeError "Bind Mis-Match"
expression (tag -> EBindAs _) = throwE $ RunTimeTypeError "Invalid Bind Construction"

-- | Interpretation of If-Then-Else constructs.
expression (tag &&& children -> (EIfThenElse, [p, t, e])) = expression p >>= \case
    VBool True -> expression t
    VBool False -> expression e
    _ -> throwE $ RunTimeTypeError "Invalid Conditional Predicate"

expression _ = throwE $ RunTimeInterpretationError "Invalid Expression"


{- Declaration interpretation -}

global :: Identifier -> K3 Type -> Maybe (K3 Expression) -> Interpretation ()
global n (tag -> TSource) (Just e)      = return ()
global n t (Just e)                     = expression e >>= modify . (:) . (n,)
global n t Nothing | TFunction <- tag t = builtin n t
global n t Nothing                      = defaultValue t >>= modify . (:) . (n,)

-- TODO: qualify names?
role :: Identifier -> [K3 Declaration] -> Interpretation ()
role n subDecls = mapM_ declaration subDecls

-- TODO
annotation :: Identifier -> [AnnMemDecl] -> Interpretation ()
annotation n members = undefined

declaration :: K3 Declaration -> Interpretation ()
declaration (tag &&& children -> (DGlobal n t eO, ch)) =
  debugDecl n t $ global n t eO >> mapM_ declaration ch
  where debugDecl n t = trace (concat ["Adding ", show n, " : ", pretty t])

declaration (tag &&& children -> (DRole r, ch)) = role r ch
declaration (tag -> DAnnotation n members)      = annotation n members

program :: K3 Declaration -> IO (Either EnvOnError IEnvironment)
program p = envOfInterpretation [] $ declaration p

runProgram :: K3 Declaration -> IO ()
runProgram p = program p >>= runInit
  where runInit (Left e) = putStrLn $ showErrorEnv e
        runInit (Right env)
          | Just (VFunction f) <- lookup "atInit" env 
          = envOfInterpretation env (f $ VTuple [])
              >>= putStrLn . either showErrorEnv showEnv
          
          | otherwise = putStrLn $ "Could not find atInit:\n" ++ showEnv env

        showErrorEnv (err, env) =
          concat $ ["Error\n", show err, "\n", showEnv env]
        
        showEnv env =
          concat $ ["Environment:\n"] ++
            map (flip (++) "\n" . show) (reverse env)


{- Built-in functions -}

ignoreFn e = VFunction $ \_ -> return e

builtin :: Identifier -> K3 Type -> Interpretation ()
builtin n t = genBuiltin n t >>= modify . (:) . (n,)

genBuiltin :: Identifier -> K3 Type -> Interpretation Value

-- parseArgs :: () -> ([String], [(String, String)])
genBuiltin "parseArgs" t =
  return $ ignoreFn $ VTuple [VCollection [], VCollection []]

-- type ChannelId = String
-- openFile :: ChannelId -> String -> String -> ()
-- openSocket :: ChannelId -> Address -> String -> ()
genBuiltin "openFile" t = return $ ignoreFn $ ignoreFn $ ignoreFn $ VTuple []
genBuiltin "openSocket" t = return $ ignoreFn $ ignoreFn $ ignoreFn $ VTuple []

-- closeFile, closeSocket :: ChannelId -> ()
genBuiltin "closeFile" t = return $ ignoreFn $ VTuple []
genBuiltin "closeSocket" t = return $ ignoreFn $ VTuple []

-- hasNext :: ChannelId -> ()
genBuiltin "hasNext" t = return $ ignoreFn $ VTuple []

-- registerSocketHandler :: ChannelId -> TTrigger () -> ()
genBuiltin "registerSocketHandler" t = return $ ignoreFn $ ignoreFn $ VTuple []

-- <source>HasNext :: () -> Bool
genBuiltin (channelMethod -> "HasNext") t = return $ ignoreFn $ VBool False

-- <source>Next :: () -> t
genBuiltin (channelMethod -> "Next") t = undefined

channelMethod :: String -> String
channelMethod x =
  case find (flip isSuffixOf x) ["HasNext", "Next"] of
    Just y -> y
    Nothing -> x


