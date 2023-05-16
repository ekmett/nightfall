{-# LANGUAGE GADTs, RoleAnnotations, RankNTypes, DataKinds, PolyKinds, TypeFamilies, TypeFamilyDependencies, BlockArguments, StandaloneDeriving, StrictData, StandaloneKindSignatures #-}

module Miden.Assembly where

import Data.Word
import Data.Kind

data N where
  Z :: N
  S :: N -> N

type Stack :: N -> Type
data Stack n where
  Nil :: Stack 'Z
  (:<) :: Word32 -> Stack n -> Stack ('S n)

infixr 5 :<

type Cmd :: (Type -> i -> j -> Type) -> j -> j -> Type
type Cmd p s s' = forall s0 c a. p c s0 s -> (p c s0 s' -> a) -> a

type Cmd1 :: (Type -> i -> j -> Type) -> Type -> j -> j -> Type
type Cmd1 p x s s' = forall s0 c a. p c s0 s -> x -> (p c s0 s' -> a) -> a

type Cmd2 :: (Type -> i -> j -> Type) -> Type -> Type -> j -> j -> Type
type Cmd2 p x y s s' = forall s0 c a. p c s0 s -> x -> y -> (p c s0 s' -> a) -> a

-- | Control frame tag for the start of execution
data Begin = Begin

-- | Control frame tag for 'if'
type If :: (Type -> N -> N -> Type) -> Type -> N -> N -> Type
newtype If t c s0 s = If (t c s0 ('S s))

-- | Control frame tag for 'else'
type Else :: (Type -> N -> N -> Type) -> Type -> N -> N -> N -> Type
newtype Else t c s0 s s' = Else (t (If t c s0 s) s s')

type Proc :: Type
data Proc = Proc String Int

type Name :: (Type -> N -> N -> Type) -> N -> N -> Type
newtype Name t i o = Name (t Proc i o)

-- | Finally-tagless encoding of Miden assembly
type M :: (Type -> N -> N -> Type) -> Constraint
class M t where
  type End t (o :: N) = (c :: Type) | c -> t
  context :: t c i o -> c

  begin :: (t Begin 'Z 'Z -> a) -> a
  end :: t Begin 'Z o -> End t o
  if_ :: t c s0 ('S s) -> (t (If t c s0 s) s s -> a) -> a
  else_ :: t (If t c s0 s) s s' -> (t (Else t c s0 s s') s s -> a) -> a
  endif :: t (Else t c s0 s s') s s' -> (t c s0 s' -> a) -> a
  push :: Cmd1 t Word32 n ('S n)
  add :: Cmd t ('S ('S n)) ('S n)
  proc :: String -> Int -> (t Proc i i -> a) -> a
  endproc :: t Proc i o -> Name t i o
  endproc = Name
  exec :: Cmd1 t (Name t i o) i o
  comment :: Cmd1 t String n n

name :: M t => Name t i o -> String
name (Name t) = case context t of
  Proc s _i -> s

-- | Useful for debugging
instance M t => Show (Name t i o) where
  showsPrec d (Name t) = case context t of
    Proc s _i -> showsPrec d s

-- | this is a direct evaluation model for interpreting Miden assembly
type E :: Type -> N -> N -> Type
data E c i o = E c (Stack i -> Stack o)

post :: (Stack s -> Stack s') -> Cmd E s s'
post f (E c s) k = k $ E c $ f . s

post1 :: (x -> Stack s -> Stack s') -> Cmd1 E x s s'
post1 f (E c s) x k = k $ E c $ f x . s

post2 :: (x -> y -> Stack s -> Stack s') -> Cmd2 E x y s s'
post2 f (E c s) x y k = k $ E c $ f x y . s

the :: Stack ('S 'Z) -> Word32
the (n :< _) = n

next :: s -> (s -> a) -> a
next s k = k s

-- | An AST representation of Miden assembly
type T :: Type -> N -> N -> Type
data T c i o where
  TBegin :: T Begin 'Z 'Z
  TIf :: T c s0 ('S s) -> T (If T c s0 s) s s
  TElse :: T (If T c s0 s) s s' -> T (Else T c s0 s s') s s
  TEndIf :: T (Else T c s0 s s') s s' -> T c s0 s'
  TPush :: T c s0 s' -> Word32 -> T c s0 ('S s')
  TAdd :: T c s0 ('S ('S n)) -> T c s0 ('S n)
  TComment :: T c s0 n -> String -> T c s0 n
  TExec :: T c s0 i -> Name T i o -> T c s0 o
  TProc :: String -> Int -> T Proc i i
deriving instance Show (T c i o)

instance M T where
  type End T o = T Begin 'Z o
  begin = next TBegin
  end x = x
  if_ x = next $ TIf x
  else_ x = next $ TElse x
  endif x = next $ TEndIf x
  push x y = next $ TPush x y
  add x = next $ TAdd x
  comment x y = next $ TComment x y
  exec x y = next $ TExec x y
  proc i o = next $ TProc i o

  context TBegin = Begin
  context (TIf x) = If x
  context (TElse x) = Else x
  context (TEndIf x) = case context x of
    Else y -> case context y of
      If z -> context z
  context (TPush x _) = context x
  context (TAdd x) = context x
  context (TComment x _) = context x
  context (TExec t _n) = context t
  context (TProc s i) = Proc s i


type Sub :: (Type -> N -> N -> Type) -> Type -> Type
type family Sub x y
type instance Sub _ Begin = Begin
type instance Sub t (If T c s0 s) = If t (Sub t c) s0 s
type instance Sub t (Else T c s0 s s') = Else t (Sub t c) s0 s s'
type instance Sub _ Proc = Proc

-- final :: M t => T c i o -> (t (Sub t c) i o -> a) -> a
-- final TBegin k = begin k
-- final (TIf x) k = _ (if_ (final x) id)

instance M E where
  type End E o = Stack o
  context (E c _) = c

  begin = next $ E Begin id
  end (E Begin f) = f Nil
  push = post1 (:<)
  add = post \(x:<y:<zs) -> (x + y):< zs
  if_ e k = k $ E (If e) id
  else_ e k = k $ E (Else e) id
  endif (E (Else (E (If (E c h)) g)) f) k = k $ E c \s0 -> case h s0 of
    b :< s -> case b of
      1 -> g s
      0 -> f s
      _ -> error $ "if.true expected 0 or 1, but received " ++ show b
  proc n locals k = k $ E (Proc n locals) id
  exec (E c f) (Name (E (Proc _n _locals) p)) k = k $ E c $ p . f
  comment = post1 \_ x -> x

-- this is a pretty-printing model
type P :: Type -> N -> N -> Type
data P c i o = P c (String -> String)

emit :: (String -> String) -> Cmd P i o
emit g (P c f) k = k $ P c $ f . g

emit1 :: (x -> String -> String) -> Cmd1 P x i o
emit1 g (P c f) i k = k $ P c $ f . g i

pp :: String -> String
pp = id

body :: Name P i o -> String
body (Name (P _ f)) = f "end"

instance M P where
  type End P o = String
  context (P c _) = c

  begin k = k $ P Begin $ showString "begin "
  end (P Begin f) = f "end"
  push = emit1 \ i -> showString "push." . showsPrec 0 i . showChar ' '
  add = emit $ showString "add "
  if_ e k = k $ P (If e) id
  else_ e k = k $ P (Else e) id
  endif (P (Else (P (If (P c h)) g)) f) k = k $ P c $
    h . showString "if.true " . g . showString "else " . f . showString "end "
  proc n locals k = k $ P (Proc n locals) $
    showString "proc." . showString n . showChar '.' . showsPrec 11 locals . showChar ' '
  exec (P c f) (Name (P (Proc n _) _)) k = k $ P c $ f . showString "exec." . showString n . showChar ' '
  comment = emit1 \ t -> foldr (\x r -> showString "# " . showString x . showChar '\n' . r) id $ lines t

