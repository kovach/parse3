module See.Tests where
import See.Types

p0 = var >> var
p1 = do
 x <- symbol "x"
 y <- symbol "y"
 unify x y
 return ()
p2 = do
 x <- symbol "x"
 y <- symbol "x"
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

p5 = do
  Subl _ _ i1 <- integerRule 2
  Subl _ _ i2 <- integerRule 3
  return ()
  unify i1 i2

-- returns 2 results (two ways to assoc), both 2 by 5
p6 = main "2 by 3 matrix * 3 by 4 matrix * 4 by 5 matrix"
