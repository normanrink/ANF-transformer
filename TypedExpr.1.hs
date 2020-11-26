{-# LANGUAGE DataKinds
           , GADTs
           , KindSignatures
           , ScopedTypeVariables
           , StandaloneDeriving
           , TypeApplications
           , TypeFamilies  
           , TypeOperators      #-}


data Type = IntT 
          | Type :-> Type
          deriving (Show)

data SType :: Type -> * where
    SIntT :: SType 'IntT
    SArrT :: SType t1 -> SType t2 -> SType (t1 ':-> t2)

deriving instance Show (SType t)


type Context = [Type]

type family App (xs :: Context) (ys :: Context) :: Context where
    App '[]       ys = ys
    App (x ': xs) ys = x ': (App xs ys)

data SContext :: Context -> * where
    SNil  :: SContext '[]
    SCons :: SType t -> SContext ctx -> SContext (t ': ctx)


data Has :: Context -> Type -> * where
    First :: Has (t ': ctx) t
    Next  :: Has ctx t -> Has (s ': ctx) t

deriving instance Show (Has ctx t)


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


data Op  = Plus | Minus | Times
         deriving (Show)


data Expr :: Context -> Type -> Class -> * where
    EInt  :: Int -> Expr ctx 'IntT c
    EVar  :: forall c t ctx. SType t -> Has ctx t -> Expr ctx t c
    EBin  :: Op -> Expr ctx 'IntT c1 -> Expr ctx 'IntT c2 -> Expr ctx 'IntT (BinClass c1 c2)
    EApp  :: Expr ctx (t1 ':-> t2) c1 -> Expr ctx t1 c2 -> Expr ctx t2 (AppClass c1 c2)
    ELet  :: Expr ctx t1 c1 -> Expr (t1 ': ctx) t2 c2 -> Expr ctx t2 (LetClass c1 c2)
    ELam  :: SType t1 -> Expr (t1 ': ctx) t2 c -> Expr ctx (t1 ':-> t2) (LamClass c)
  
deriving instance Show (Expr ctx t c)

type ImmExpr ctx t = Expr ctx t 'Imm
type AnfExpr ctx t = Expr ctx t 'Anf


stype :: Expr ctx t c -> SType t
stype (EInt _)     = SIntT
stype (EVar st _)  = st
stype (EBin _ _ _) = SIntT
stype (EApp e1 _)  =
    case stype e1 of
        SArrT _ st2 -> st2
stype (ELet _ e2)  = stype e2
stype (ELam st1 e) = SArrT st1 (stype e)


shiftHas :: SContext ctx0 -> SType s -> SContext ctx1
         -> Has (App ctx0 ctx1) t -> Has (App ctx0 (s ': ctx1)) t
shiftHas SNil         _  _  First    = Next First 
shiftHas (SCons _ _)  _  _  First    = First
shiftHas SNil         _  _  (Next h) = Next (Next h)
shiftHas (SCons _ ts) st sc (Next h) = Next $ shiftHas ts st sc h

shiftExpr :: SContext ctx0 -> SType s -> SContext ctx1
          -> Expr (App ctx0 ctx1) t c -> Expr (App ctx0 (s ': ctx1)) t c
shiftExpr _   _  _   (EInt n)        = EInt n
shiftExpr sc0 st sc1 (EVar stv x)    = EVar stv (shiftHas sc0 st sc1 x) 
shiftExpr sc0 st sc1 (EBin op e1 e2) = EBin op (shiftExpr sc0 st sc1 e1) 
                                               (shiftExpr sc0 st sc1 e2)
shiftExpr sc0 st sc1 (EApp e1 e2)    = EApp (shiftExpr sc0 st sc1 e1) 
                                            (shiftExpr sc0 st sc1 e2)
shiftExpr sc0 st sc1 (ELet e1 e2)    = ELet (shiftExpr sc0 st sc1 e1)
                                            (shiftExpr (SCons (stype e1) sc0) st sc1 e2)
shiftExpr sc0 st sc1 (ELam stl e)    = ELam stl (shiftExpr (SCons stl sc0) st sc1 e)


anf :: SContext ctx -> Expr ctx t c -> AnfExpr ctx t
anf _  (EInt n) = EInt n
anf _  (EVar st x) = EVar st x
anf sc (ELet e1 e2) = 
    let a1 = anf sc e1
        a2 = anf (SCons (stype e1) sc) e2
    in ELet a1 a2
anf sc (ELam st e) = 
    let a = anf (SCons st sc) e
    in ELam st a
anf sc (EBin o e1 e2) =
    let v1 = shiftExpr SNil SIntT sc $ anf sc e1
        v2 = anf sc e2
        bo = EBin o (EVar @'Imm SIntT First)
                    (EVar @'Imm SIntT (Next First))
    in ELet v2 (ELet v1 bo)            
anf sc (EApp e1 e2) =
    let v1 = shiftExpr SNil (stype e2) sc $ anf sc e1
        v2 = anf sc e2
        ap = EApp (EVar @'Imm (stype e1) First) 
                  (EVar @'Imm (stype e2) (Next First))
    in ELet v2 (ELet v1 ap)

toAnf :: Expr '[] t c -> AnfExpr '[] t
toAnf e = anf SNil e

type IntExpr = Expr '[] 'IntT 'Imm

srcExpr :: Expr '[] 'IntT 'Top
srcExpr = EBin Times
            (EBin Times
              (EBin Plus  (EInt  2 :: IntExpr) (EInt 3 :: IntExpr))
              (EBin Minus (EInt 12 :: IntExpr) (EInt 4 :: IntExpr)))
            (EBin Plus (EInt 7) (EInt 8))

--
-- toAnf srcExpr =
--
-- ELet 
--     (ELet (EInt 8) 
--           (ELet (EInt 7) 
--                 (EBin Plus (EVar SIntT First) (EVar SIntT (Next First)))
--           )
--     ) 
--     (ELet 
--         (ELet 
--             (ELet (EInt 4) 
--                   (ELet (EInt 12)
--                         (EBin Minus (EVar SIntT First) (EVar SIntT (Next First)))
--                   )
--             )
--             (ELet
--                 (ELet (EInt 3) 
--                       (ELet (EInt 2) 
--                             (EBin Plus (EVar SIntT First) (EVar SIntT (Next First)))
--                       )
--                 ) 
--                 (EBin Times (EVar SIntT First) (EVar SIntT (Next First)))
--             )
--         )
--         (EBin Times (EVar SIntT First) (EVar SIntT (Next First)))
--     )