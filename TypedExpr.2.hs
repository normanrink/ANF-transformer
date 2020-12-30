{-# LANGUAGE DataKinds
           , GADTs
           , PolyKinds
           , RankNTypes
           , StandaloneDeriving
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

sappend :: SContext ctx1 -> SContext ctx2 -> SContext (App ctx1 ctx2)
sappend SNil           sc2 = sc2
sappend (SCons st sc1) sc2 = SCons st (sappend sc1 sc2)


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
    EVar  :: SType t -> Has ctx t -> Expr ctx t c
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
stype (EApp e1 _)  = case stype e1 of
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

shiftExpr' :: SContext ctx0 -> SContext ctx' -> SContext ctx1
           -> Expr (App ctx0 ctx1) t c -> Expr (App ctx0 (App ctx' ctx1)) t c
shiftExpr' _   SNil           _   e = e
shiftExpr' sc0 (SCons st sc') sc1 e = let e' = shiftExpr' sc0 sc' sc1 e
                                      in shiftExpr sc0 st (sappend sc' sc1) e'


data (a :: k) :~: (b :: k) where
    Refl :: a :~: a

appAssoc :: SContext ts1 -> SContext ts2 -> SContext ts3
         -> App ts1 (App ts2 ts3) :~: App (App ts1 ts2) ts3
appAssoc SNil SNil           _    = Refl
appAssoc SNil (SCons _ sts2) sts3 = 
    case appAssoc SNil sts2 sts3 of
        Refl -> Refl
appAssoc (SCons _ sts1) sts2 sts3 =
    case appAssoc sts1 sts2 sts3 of
        Refl -> Refl

exprCtxAssoc1 :: SContext ts1 -> SContext ts2 -> SContext ts3
              -> Expr (App ts1 (App ts2 ts3)) t c ->  Expr (App (App ts1 ts2) ts3) t c
exprCtxAssoc1 sts1 sts2 sts3 e = 
    case appAssoc sts1 sts2 sts3 of
        Refl -> e

exprCtxAssoc2 :: SContext ts1 -> SContext ts2 -> SContext ts3
              -> Expr (App (App ts1 ts2) ts3) t c -> Expr (App ts1 (App ts2 ts3)) t c
exprCtxAssoc2 sts1 sts2 sts3 e = 
    case appAssoc sts1 sts2 sts3 of
        Refl -> e


data Env :: Context -> Class -> Context -> * where
    EnvNil  :: Env ctx c '[]
    EnvCons :: Expr (App ts ctx) t c -> Env ctx c ts -> Env ctx c (t ': ts)

eappend :: SContext ctx -> SContext ts1 -> SContext ts2
        -> Env ctx c ts1 -> Env ctx c ts2 -> Env ctx c (App ts1 ts2)
eappend _  _             _   EnvNil          env' = env'
eappend sc (SCons _ sc1) sc2 (EnvCons e env) env' = 
    let env'' = eappend sc sc1 sc2 env env'
        e'  = shiftExpr' sc1 sc2 sc e
        e'' = exprCtxAssoc1 sc1 sc2 sc e'
    in EnvCons e'' env''

type AnfEnv ctx ts = Env ctx 'Anf ts

data EnvExpr cEnv cExpr ctx t =
    forall (ts :: Context). EnvExpr (SContext ts) 
                                    (Env ctx cEnv ts)
                                    (Expr (App ts ctx) t cExpr)

type AnfEnvImmExpr ctx t = EnvExpr 'Anf 'Imm ctx t


anf :: SContext ctx -> Expr ctx t c -> AnfExpr ctx t
anf _ (EInt n) = EInt n
anf _ (EVar st x) = EVar st x
anf sc (ELet e1 e2) = 
    let a1 = anf sc e1
        a2 = anf (SCons (stype e1) sc) e2
    in ELet a1 a2
anf sc (ELam st e) = 
    let a = anf (SCons st sc) e
    in ELam st a
anf sc (EBin op e1 e2) =
    case imm sc e1 of
        EnvExpr tsc1 env1 v1 ->
            case imm sc e2 of
                EnvExpr tsc2 env2 v2 ->
                    let env = eappend sc tsc2 tsc1 env2 env1
                        v1' = shiftExpr' SNil tsc2 (sappend tsc1 sc) v1
                        v2' = shiftExpr' tsc2 tsc1 sc v2 
                        e' = EBin op v1' v2'
                        e'' = exprCtxAssoc1 tsc2 tsc1 sc e'
                        ee = EnvExpr (sappend tsc2 tsc1) env e''
                    in mkLet sc ee
anf sc (EApp e1 e2) =
    case imm sc e1 of
        EnvExpr tsc1 env1 v1 ->
            case imm sc e2 of
                EnvExpr tsc2 env2 v2 ->
                    let env = eappend sc tsc2 tsc1 env2 env1
                        v1' = shiftExpr' SNil tsc2 (sappend tsc1 sc) v1
                        v2' = shiftExpr' tsc2 tsc1 sc v2 
                        e' = EApp v1' v2'
                        e'' = exprCtxAssoc1 tsc2 tsc1 sc e'
                        ee = EnvExpr (sappend tsc2 tsc1) env e''
                    in mkLet sc ee

mkLet :: SContext ctx -> EnvExpr 'Anf 'Anf ctx t -> AnfExpr ctx t
mkLet _  (EnvExpr SNil          EnvNil           e) = e
mkLet sc (EnvExpr (SCons _ sts) (EnvCons e' env) e) =
    let ee = ELet e' e
    in mkLet sc (EnvExpr sts env ee)

imm :: SContext ctx -> Expr ctx t c -> AnfEnvImmExpr ctx t
imm _  (EInt n)       = EnvExpr SNil EnvNil (EInt n)
imm _  (EVar st x)    = EnvExpr SNil EnvNil (EVar st x)
imm sc e@ELet {}      = let (env, e') = immExpr sc e
                            tsc = SCons (stype e) SNil
                        in EnvExpr tsc env e'
imm sc e@ELam {}      = let (env, e') = immExpr sc e
                            tsc = SCons (stype e) SNil
                        in EnvExpr tsc env e'
imm sc (EBin o e1 e2) = imm2 sc e1 e2 (EBin o)
imm sc (EApp e1 e2)   = imm2 sc e1 e2 EApp

immExpr :: SContext ctx -> Expr ctx t c -> (AnfEnv ctx '[t], ImmExpr (t ': ctx) t)
immExpr sc e = 
  let a = anf sc e
      env = EnvCons a EnvNil
      v = EVar (stype e) First
  in (env, v)

imm2 :: SContext ctx 
     -> Expr ctx t1 c1 -> Expr ctx t2 c2 
     -> (forall ctx'. ImmExpr ctx' t1 -> ImmExpr ctx' t2 -> AnfExpr ctx' t)
     -> AnfEnvImmExpr ctx t
imm2 sc e1 e2 f =
    case imm sc e1 of
        EnvExpr tsc1 env1 v1 -> 
            case imm sc e2 of
                EnvExpr tsc2  env2 v2 -> 
                    let env = eappend sc tsc2 tsc1 env2 env1
                        v1' = shiftExpr' SNil tsc2 (sappend tsc1 sc) v1
                        v2' = shiftExpr' tsc2 tsc1 sc v2 
                        e = f v1' v2'
                        e' = exprCtxAssoc1 tsc2 tsc1 sc e 
                        ve' = EVar (stype e') First
                        env' = EnvCons e' env
                        sc' = SCons (stype e') (sappend tsc2 tsc1)
                    in EnvExpr sc' env' ve'

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
-- ELet (EBin Plus (EInt 2) (EInt 3))
--      (ELet (EBin Minus (EInt 12) (EInt 4))
--            (ELet (EBin Times (EVar SIntT (Next First)) (EVar SIntT First))
--                  (ELet (EBin Plus (EInt 7) (EInt 8))
--                        (EBin Times (EVar SIntT (Next First)) (EVar SIntT First))
--                  )
--            )
--      )


substHas :: SContext ctx0 -> SType t -> SContext ctx1
         -> Expr ctx1 s c -> Has (App ctx0 (s ': ctx1)) t
         -> Expr (App ctx0 ctx1) t c
substHas SNil           _  _   es First    = es 
substHas SNil           st _   _  (Next x) = EVar st x
substHas (SCons _ _)    st _   _  First    = EVar st First
substHas (SCons s0 sc0) st sc1 es (Next x) =
    let e = substHas sc0 st sc1 es x
    in shiftExpr SNil s0 (sappend sc0 sc1) e

relax :: Expr ctx t c -> Expr ctx t 'Top
relax (EInt n)        = EInt n
relax (EVar st x)     = EVar st x
relax (ELet e1 e2)    = ELet (relax e1) (relax e2)
relax (ELam st e)     = ELam st (relax e)
relax (EBin op e1 e2) = EBin op (relax e1) (relax e2)
relax (EApp e1 e2)    = EApp (relax e1) (relax e2)

subst :: SContext ctx0 -> SContext ctx1
      -> Expr ctx1 s c1 -> Expr (App ctx0 (s ': ctx1)) t c2
      -> Expr (App ctx0 ctx1) t 'Top
subst _   _   _  (EInt n)    = EInt n
subst sc0 sc1 es (EVar st x) = relax $ substHas sc0 st sc1 es x
subst sc0 sc1 es (ELet e1 e2) = 
    let e1' = subst sc0 sc1 es e1
        e2' = subst (SCons (stype e1) sc0) sc1 es e2
    in ELet e1' e2'
subst sc0 sc1 es (ELam st e) = 
    let e' = subst (SCons st sc0) sc1 es e
    in ELam st e'
subst sc0 sc1 es (EBin op e1 e2) =
    let e1' = subst sc0 sc1 es e1
        e2' = subst sc0 sc1 es e2
    in EBin op e1' e2'
subst sc0 sc1 es (EApp e1 e2) =
    let e1' = subst sc0 sc1 es e1
        e2' = subst sc0 sc1 es e2
    in EApp e1' e2'

eval :: SContext ctx -> Expr ctx t c -> Expr ctx t 'Top
eval _  (EInt n)        = EInt n
eval _  (EVar st x)     = EVar st x 
eval sc (ELet e1 e2)    = let e1' = eval sc e1
                              se  = subst SNil sc e1' e2
                          in eval sc se
eval _  (ELam st e)     = ELam st (relax e)
eval sc (EBin op e1 e2) = let EInt n1 = eval sc e1
                              EInt n2 = eval sc e2
                          in case op of
                               Plus -> EInt (n1 + n2)
                               Minus -> EInt (n1 - n2)
                               Times -> EInt (n1 * n2)
eval sc (EApp e1 e2) = case eval sc e1 of
                            ELam _ e -> let e2' = eval sc e2
                                            se = subst SNil sc e2' e
                                        in eval sc se
