module See.Definition where
import See.Types

import qualified Data.Traversable as T (Traversable, mapAccumR, sequence, mapM)
import Control.Applicative ((<$>), (<*>))
import Control.Monad
import Control.Monad.Free
import Data.List (sort)

-- Form closure of term
-- Should yield complete subgraph that defines it,
-- suitable for reinterpret.
packBlock :: Name -> VM Name
packBlock name = do
  cs <- sort <$> allChildren name
  copyVals name cs

-- INCLUDES properties
allChildren :: Name -> VM [Name]
allChildren name = do
  val <- get name
  let names = children val
  rest <- mapM allChildren names
  props <- propertyNames name
  return $ names ++ props ++ concat rest

buildVal :: Name -> VM (Free Val Name)
buildVal name = fmap wrap (get name >>= T.mapM buildVal)

-- Takes a subgraph and recreates it.
-- Should be equivalent to rerunning the VM action that added it.
--reinterpret :: Name -> VM ()
--reinterpret block = do
--  Block start end <- get block
--  names <- getRange start end
--  foldM copyVal' [] names
--  return ()

type Rename = [(Name, Name)]
copyVal' :: Rename -> Name -> VM Rename
copyVal' m n = do
  (m', _) <- copyVal m n
  return m'
copyVal :: Rename -> Name -> VM (Rename, Name)
copyVal mapping name = do
  val <- get name
  name' <- store (fmap fix val)
  return ((name, name') : mapping, name')
  where
    fix n | Just n' <- lookup n mapping = n'
    fix n = n

copyVals :: Name -> [Name] -> VM Name
copyVals root names = do
  mapping <- foldM copyVal' [] names
  (_, root') <- copyVal mapping root
  return root'

getRange :: Name -> Name -> UM a [a]
getRange = undefined

-- Vocab needed
-- a
--   a _type_        -> val
--   a _type_ _val_  -> val
-- is, =
--   _val1_ is _val2_ -> unify val1 val2, return no object
-- where
--   _a_ where _b_ -> no op?
-- set -> just a basic object
-- in
--   _symbol_ in _type=set_
--
-- tuple syntax ( , ). base it on , ?
--   ( _val1_ , _val2_ )  -> tuple
--   pre , post
--
-- and?
--
--
-- e.g.
-- def square: a square matrix is a n by n matrix.
-- def graph: a graph is a pair (V, E).
--   V is a set.
--   e in E is a (V, V).
