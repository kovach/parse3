module See.Tests where
import See.Types
import qualified Data.Map as M

-- Testing
main :: String -> IO ()
main = main_ True
main' :: String -> IO ()
main' = main_ False
main_ :: Bool -> String -> IO ()
main_ closed str = chk $ do
  context <- parse str
  -- get result

  -- If closed is true, parsing will fail unless stack contains exactly one
  -- element
  if closed then do
    stack <- topStack context
    val <- pop stack
    isEmpty stack 
    return (Just val) else
    return Nothing

chk :: Show a => VM a -> IO ()
chk m =
  let worlds = runUM m
      (values, _) = unzip worlds
  in do
    mapM_
      (\(value, (_, env)) -> do
        putStrLn ">>>>>>>"
        mapM_ print (M.toList env)
        putStrLn "<<<<<<<"
        putStrLn ("VALUE: " ++ show value))
      worlds
    putStrLn ("-------\nPARSE COUNT: " ++ show (length values))


p0 = var >> var
p1, p2, p4 :: VM ()
p1 = do
 x <- symbolLit "x"
 y <- symbolLit "y"
 unify x y
 return ()
p2 = do
 x <- symbolLit "x"
 y <- symbolLit "x"
 z <- var
 unify x y
 unify y z
 return ()
p4 = do
  nil <- store Nil
  s <- store (Ptr nil)
  let stack = Stack s
  v1 <- var
  v2 <- var
  push stack v1
  push stack v2
  _ <- pop stack
  return ()

twopair = do
  p1 <- var
  p2 <- var
  (h1, t1) <- isCons p1
  (h2, t2) <- isCons p2
  unify p1 p2
  return h1
pp :: VM Name
pp = do
  h1 <- twopair
  num <- store $ IntLit 22
  v <- storeList [num]
  --num' <- store $ IntLit 23
  --v' <- singleton num
  unify h1 v
  --unify h2 v'
  return h1
p7 = do
  x <- store $ IntLit 0
  y <- store $ IntLit 1
  z <- store $ IntLit 2
  storeList [x,y,z]

-- returns 2 results (two ways to assoc), both 2 by 5
p6 = main "2 by 3 matrix * 3 by 4 matrix * 4 by 5 matrix"

