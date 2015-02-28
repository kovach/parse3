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


