-- TODO clean up imports
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module See.Types where

import qualified Data.Map as M
import Control.Monad
import Control.Monad.State hiding (get, put)
import qualified Control.Monad.State as S (get, put)
import Control.Applicative ((<$>), (<*>))
import Data.Maybe (fromJust, mapMaybe)
import qualified Data.Traversable as T (Traversable, mapAccumR)
import Data.Foldable (Foldable)
import Text.Read (readMaybe)
import Debug.Trace (trace)

-- Environment stuff
-- TODO move to Monad.Condition
newtype Name = N Integer
 deriving (Eq, Ord)

instance Show Name where
  show (N i) = "#" ++ show i

type UState a = (Integer, M.Map Name a)
emptyChain :: UState a
emptyChain = (0, M.empty)

type UM a = StateT (UState a) [] 
runUM :: UM s a -> [(a, UState s)]
runUM m = runStateT m emptyChain

get :: Name -> UM a a
get name = do
  (_, m) <- S.get
  return $ fromJust . M.lookup name $ m

store :: a -> UM a Name
store val = do
  (count, env) <- S.get
  let name = N (count + 1)
  S.put (count + 1, M.insert name val env)
  return name

put :: Name -> a -> UM a ()
put name val = modify $ \(c, env) -> (c, M.insert name val env)

-- Returns all objects that refer to given name
refs :: (Name -> a -> Maybe b) -> UM a [b]
refs fn = do
  (_, env) <- S.get
  return $ mapMaybe (uncurry fn) $ M.toList env

modifyAll :: (Name -> a -> a) -> UM a ()
modifyAll fn = do
  (c, env) <- S.get
  S.put (c, M.mapWithKey fn env)

getEnv :: UM a [(Name, a)]
getEnv = M.toList . snd <$> S.get

-----------------------------
-- Core Internal Structure --
-----------------------------
type Tag = String

-- Used to represent object properties
-- [root]'s [tag] property is [object]
data Link a = Link
  { tag :: Tag
  , root :: a
  , object :: a
  }
 deriving (Eq, Ord, Show, Functor, Foldable, T.Traversable)

-- "preconditions", "postconditions", resultant object
data Subl a = Subl
  { pre :: a
  , post :: a
  , output :: Command a
  }
 deriving (Eq, Ord, Show, Functor, Foldable, T.Traversable)

data Command a
  = Push a | DoSub (Subl a)
  | CreateFrame a | CloseFrame
  | DoNothing
 deriving (Eq, Ord, Show, Functor, Foldable, T.Traversable)


-- Core datatype
data Val a
  = Var
  | Ref Name
  | Val Tag
  | Prop (Link a)
  | Sub (Subl a)
  -- Stacks
  | Nil
  | Cons a a
  | Ptr a
  -- Literals
  | IntLit Integer
  | Symbol Tag
  -- Contexts
  | Binding Tag a
  -- TODO make these stack arguments?
  | Frame (Maybe Tag) a a -- parse stack, environment stack, special word
 deriving (Eq, Ord, Show, Functor, Foldable, T.Traversable)

-- This Name should point to a Ptr value
newtype Stack = Stack Name
  deriving (Show, Eq, Ord)

-- Should be a stack of stacks
newtype Context = Context Stack
  deriving (Show, Eq, Ord)

-- Primary monad type
type VM = UM (Val Name)
------------------------
-- End Core Structure --
------------------------

type Rule = VM (Subl Name)

type Word = String
type Parser = Word -> Maybe Rule
type Dict = [Parser]

-- Tree utilities
tagEq :: (Functor f, Eq (f ())) => f a -> f a -> Bool
tagEq t1 t2 = fmap (const ()) t1 == fmap (const ()) t2

children :: (T.Traversable t) => t a -> [a]
children t = fst $ T.mapAccumR step [] t
 where
  step list child = (child : list, ())

-- Property Utilities --
properties :: Name -> VM [Link Name]
properties n = mapM get' =<< propertyNames n
 where
   get' n = do
     Prop l <- get n
     return l

propertyNames :: Name -> VM [Name]
propertyNames root = do
  refs isProp
 where
  isProp name (Prop l@(Link {root = r})) | r == root = Just name
  isProp _ _ = Nothing

getProperty :: Name -> Tag -> VM Name
getProperty name tag = do
  ps <- properties name
  -- Failure kills the branch
  [val] <- return $ mapMaybe select ps
  return val
 where
   select (Link {tag = t, object = o}) | t == tag = Just o
   select _ = Nothing

