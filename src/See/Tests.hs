module See.Tests where
import See.Types
import See.Primitives
import See.Parse
import See.Definition
import qualified Data.Map as M

import Data.Either (isLeft, isRight, partitionEithers)
import Data.List (sort, sortBy)

-- Testing
main :: String -> IO ()
main = main_ True
main' :: String -> IO ()
main' = main_ False
main_ :: Bool -> String -> IO ()
main_ closed str = chk $ do
  (context, assignments) <- parseMain str
  -- get result

  -- If closed is true, parsing will fail unless stack contains exactly one
  -- element
  if closed then do
    stack <- topStack context
    val <- pop stack
    isEmpty stack 
    isVal val
    return $ Just (val, assignments) else
    return Nothing

  --let Context c = context
  --str <- printVal $ stackName c
  --return (Just str)


printVal n = do
  val <- get n
  case val of
    Ptr n -> printStack n
    _ -> return $ show val

-- TODO
printStack s = do
  list <- get s
  case list of
    Var -> return "VAR"
    Nil -> return "."
    Cons x xs -> do
      s1 <- printVal x
      s2 <- printVal xs
      return (s1 ++ "\n" ++ s2)
    _ -> error (show list)


sortWith f = sortBy (\x y -> compare (f x) (f y))

chk :: Show a => VM a -> IO ()
chk m =
  let 
      outcomes = runVM m
      (values, _) = unzip outcomes
      lf :: (Either a b, c) -> Either a (b, c)
      lf (ma, b) = do
        a <- ma
        return (a, b)
      printSuccess (value, (_, env)) = do
        putStrLn ">>>>>>>"
        mapM_ print (M.toList env)
        putStrLn "<<<<<<<"
        print value

      (_, successes) = partitionEithers (map lf outcomes)
      failures = reverse $ sortWith (fst . snd) $ filter (isLeft . fst) outcomes

      --failLengths = reverse . sort . map (fst . snd) $ failures

      printFailure (Left err, (count, _)) =
        putStrLn $ "Left: " ++ show count ++ " " ++ err

      sep = putStrLn "--------------------------------"

  in do
    mapM_ printSuccess $ successes
    sep
    putStrLn $ "FAILED PARSES: " ++ show (length failures)
    mapM_ printFailure $ take 5 failures
    sep
    putStrLn $ "PARSE COUNT: " ++ show (length successes)
    sep


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

pb = do
  p1 <- var
  p2 <- var
  s <- store (Cons p1 p2)
  s' <- packBlock s
  s'' <- packBlock s'
  return s''


-- returns 2 results (two ways to assoc), both 2 by 5
p6 = main "2 by 3 matrix * 3 by 4 matrix * 4 by 5 matrix"

