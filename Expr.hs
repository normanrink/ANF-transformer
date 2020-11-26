-- This file is based on the source code presented
-- in the Liquid Haskell blog on A-normal form,
-- cf. https://ucsd-progsys.github.io/liquidhaskell-blog/2016/09/01/normal-forms.lhs/.

{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , StandaloneDeriving
           , TypeFamilies       #-}

import Control.Monad.State.Lazy


data Class = Imm  -- Immediate
           | Anf  -- ANF
           | Top  -- Top, i.e. unconstrained expression
           deriving (Show)

type family BinClass (c1 :: Class) (c2 :: Class) :: Class where
    BinClass 'Imm 'Imm = 'Anf
    BinClass _    _    = 'Top

type family AppClass (c1 :: Class) (c2 :: Class) :: Class where
    AppClass 'Imm 'Imm = 'Anf
    AppClass _    _    = 'Top

type family LetClass (c1 :: Class) (c2 :: Class) :: Class where
    LetClass 'Anf 'Anf = 'Anf
    LetClass _    _    = 'Top

type family LamClass (c :: Class) :: Class where
    LamClass 'Anf = 'Anf
    LamClass _    = 'Top


data Expr :: Class -> * where
    EInt  :: Int -> Expr c
    EVar  :: Var -> Expr c
    EBin  :: Op  -> Expr c1 -> Expr c2 -> Expr (BinClass c1 c2)
    EApp  :: Expr c1 -> Expr c2 -> Expr (AppClass c1 c2)
    ELet  :: Var -> Expr c1 -> Expr c2 -> Expr (LetClass c1 c2)
    ELam  :: Var -> Expr c -> Expr (LamClass c)
  
deriving instance Show (Expr c)

type Var = String

data Op  = Plus | Minus | Times
         deriving (Show)

type AnfM a = State Int a

fresh :: AnfM Var
fresh = do
  n <- get
  put (n+1)
  return ("anf" ++ show n)

type ImmExpr = Expr 'Imm
type AnfExpr = Expr 'Anf


anf :: Expr c -> AnfM AnfExpr
anf (EInt n) = return (EInt n)
anf (EVar x) = return (EVar x)
anf (ELet x e1 e2) = do
  a1 <- anf e1
  a2 <- anf e2
  return (ELet x a1 a2)
anf (EBin o e1 e2) = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  return (mkLet (b1s ++ b2s) (EBin o v1 v2))
anf (ELam x e) = do
  a <- anf e
  return (ELam x a)
anf (EApp e1 e2) = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  return (mkLet (b1s ++ b2s) (EApp v1 v2))

mkLet :: [(Var, AnfExpr)] -> AnfExpr -> AnfExpr
mkLet []         e' = e'
mkLet ((x,e):bs) e' = ELet x e (mkLet bs e')

imm :: Expr c -> AnfM ([(Var, AnfExpr)], ImmExpr)
imm (EInt n)       = return ([], EInt n)
imm (EVar x)       = return ([], EVar x)
imm e@(ELet {})    = immExpr e
imm e@(ELam {})    = immExpr e
imm (EBin o e1 e2) = imm2 e1 e2 (EBin o)
imm (EApp e1 e2)   = imm2 e1 e2 EApp

immExpr :: Expr c -> AnfM ([(Var, AnfExpr)], ImmExpr)
immExpr e = do
  a <- anf e
  t <- fresh
  return ([(t, a)], EVar t)

imm2 :: Expr c1 -> Expr c2 
     -> (ImmExpr -> ImmExpr -> AnfExpr)
     -> AnfM ([(Var, AnfExpr)], ImmExpr)
imm2 e1 e2 f = do
  (b1s, v1) <- imm e1
  (b2s, v2) <- imm e2
  t         <- fresh
  let bs'    = b1s ++ b2s ++ [(t, f v1 v2)]
  return      (bs', EVar t)

toAnf :: Expr c -> AnfExpr
toAnf e = evalState (anf e) 0

srcExpr :: Expr 'Top
srcExpr = EBin Times
            (EBin Times
              (EBin Plus  (EInt  2 :: ImmExpr) (EInt 3 :: ImmExpr))
              (EBin Minus (EInt 12 :: ImmExpr) (EInt 4 :: ImmExpr)))
            (EBin Plus (EInt 7 :: ImmExpr) (EInt 8 :: ImmExpr))

--
-- toAnf srcExpr =
--
-- ELet "anf0" 
--      (EBin Plus (EInt 2) (EInt 3))
--      (ELet "anf1"
--            (EBin Minus (EInt 12) (EInt 4))
--            (ELet "anf2"
--                  (EBin Times (EVar "anf0") (EVar "anf1"))
--                  (ELet "anf3"
--                        (EBin Plus (EInt 7) (EInt 8))
--                        (EBin Times (EVar "anf2") (EVar "anf3"))
--                  )
--            )
--      )