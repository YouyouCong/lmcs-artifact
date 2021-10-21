-- Formalization of fine-grained λF

module LambdaF-FG where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality

-- Expression types
data Ty : Set

-- Trail types
data Tr : Set

data Ty where
  Nat          : Ty
  Bool         : Ty
  Str          : Ty
  _⇒p_         : Ty → Ty → Ty
  _⇒i_⟨_⟩_⟨_⟩_ : Ty → Ty → Tr → Ty → Tr → Ty → Ty

data Tr where
  ●      : Tr
  _⇒⟨_⟩_ : Ty → Tr → Ty → Tr

-- Auxiliary relations
-- id-cont-type τ μ τ' means the type τ → μ → τ' is consistent
-- with the identity continuation
id-cont-type : Ty → Tr → Ty → Set
id-cont-type τ ● τ' = τ ≡ τ'
id-cont-type τ (τ₁ ⇒⟨ μ ⟩ τ₁') τ' = τ ≡ τ₁ × τ' ≡ τ₁' × μ ≡ ●

-- compatible μ₁ μ₂ μ₃ means composing a μ₁-context with a μ₂-context
-- results in a μ₃-context
compatible : Tr → Tr → Tr → Set
compatible ● μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') ● μ₃ = (τ₁ ⇒⟨ μ₁ ⟩ τ₁') ≡ μ₃
compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') (τ₂ ⇒⟨ μ₂ ⟩ τ₂') ● = ⊥
compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') (τ₂ ⇒⟨ μ₂ ⟩ τ₂') (τ₃ ⇒⟨ μ₃ ⟩ τ₃') =
  τ₁ ≡ τ₃ × τ₁' ≡ τ₃' × compatible (τ₂ ⇒⟨ μ₂ ⟩ τ₂') μ₃ μ₁

-- Values and expressions
-- e : Exp var τ μα α μβ β means that e
--  * has type τ
--  * requires a τ-to-α context awaiting a μα-trail
--  * requires a μβ-trail
--  * eventually produces a β-value
data Val[_]_ (var : Ty → Set) : Ty → Set
data PExp[_]_ (var : Ty → Set) : Ty → Set
data IExp[_]_⟨_⟩_⟨_⟩_ (var : Ty → Set) : Ty → Tr → Ty → Tr → Ty → Set

data Val[_]_ var where
  Var     : {τ : Ty} → var τ → Val[ var ] τ
  Num     : ℕ → Val[ var ] Nat
  Bol     : 𝔹 → Val[ var ] Bool
  Str     : String → Val[ var ] Str
  PAbs    : {τ₁ τ₂ : Ty} →
            (var τ₁ → PExp[ var ] τ₂) →
            Val[ var ] (τ₁ ⇒p τ₂)
  IAbs    : {τ₁ τ₂ α β : Ty} {μα μβ : Tr} →
            (var τ₁ → IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            Val[ var ] (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β)

data PExp[_]_ var where
  Val     : {τ : Ty} → Val[ var ] τ → PExp[ var ] τ
  PApp    : {τ₁ τ₂ : Ty} →
            PExp[ var ] (τ₁ ⇒p τ₂) → PExp[ var ] τ₁ →
            PExp[ var ] τ₂
  PPlus   : PExp[ var ] Nat → PExp[ var ] Nat →
            PExp[ var ] Nat
  PIs0    : PExp[ var ] Nat → PExp[ var ] Bool
  PB2S    : PExp[ var ] Bool → PExp[ var ] Str
  Prompt : {τ β β' : Ty} {μᵢ : Tr} →
            id-cont-type β μᵢ β' →
            IExp[ var ] β ⟨ μᵢ ⟩ β' ⟨ ● ⟩ τ →
            PExp[ var ] τ

data IExp[_]_⟨_⟩_⟨_⟩_ var where
  Exp     : {τ α : Ty} {μα : Tr} →
            PExp[ var ] τ → IExp[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ α
  PIApp   : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
            IExp[ var ] (τ₁ ⇒p τ₂) ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            IExp[ var ] τ₁ ⟨ μγ ⟩ γ ⟨ μα ⟩ α →
            IExp[ var ] τ₂ ⟨ μγ ⟩ γ ⟨ μβ ⟩ β
  IApp    : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
            IExp[ var ] (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ →
            IExp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ →
            IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μδ ⟩ δ
  IPlus   : {α β γ : Ty} {μα μβ μγ : Tr} →
            IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            IExp[ var ] Nat ⟨ μγ ⟩ γ ⟨ μα ⟩ α →
            IExp[ var ] Nat ⟨ μγ ⟩ γ ⟨ μβ ⟩ β
  IIs0    : {α β : Ty} {μα μβ : Tr} →
            IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            IExp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β
  IB2S    : {α β : Ty} {μα μβ : Tr} →
            IExp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            IExp[ var ] Str ⟨ μα ⟩ α ⟨ μβ ⟩ β
  PControl : {τ α β γ γ' : Ty} {μᵢ μα : Tr} →
             id-cont-type γ μᵢ γ' →
             (var (τ ⇒p α) → IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) →
             IExp[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ β
  IControl : {τ α β γ γ' τ₁ τ₁' : Ty} {μᵢ μ₀ μ₁ μ₂ μα μβ : Tr} →
             id-cont-type γ μᵢ γ' →
             compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') μ₂ μ₀ →
             compatible μβ μ₀ μα →
             (var (τ ⇒i τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α) →
              IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) →
             IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β


-- CPS interpreter

-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛μ : Tr → Set

〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 Str 〛τ = String
〚 τ₁ ⇒p τ₂ 〛τ = 〚 τ₁ 〛τ → 〚 τ₂ 〛τ
〚 τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β 〛τ =
  〚 τ₁ 〛τ → (〚 τ₂ 〛τ → 〚 μα 〛μ → 〚 α 〛τ) → 〚 μβ 〛μ → 〚 β 〛τ

〚 ● 〛μ = ⊤
〚 τ ⇒⟨ μ ⟩ τ' 〛μ = 〚 τ 〛τ → 〚 μ 〛μ → 〚 τ' 〛τ

-- Identity continuation
kid : {τ τ' : Ty} {μ : Tr} →
      id-cont-type τ μ τ' →
      〚 τ 〛τ → 〚 μ 〛μ → 〚 τ' 〛τ
kid {μ = ●} refl v tt = v
kid {μ = τ₁ ⇒⟨ .● ⟩ τ₁'} (refl , refl , refl) v k = k v tt

-- Trail composition
append : {μ₁ μ₂ μ₃ : Tr} →
         compatible μ₁ μ₂ μ₃ → 〚 μ₁ 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ

cons : {τ₁ τ₁' : Ty} {μ₁ μ₂ μ₃ : Tr} →
       compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') μ₂ μ₃ → 〚 τ₁ ⇒⟨ μ₁ ⟩ τ₁' 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ

append {●} refl tt t₂ = t₂
append {τ₁ ⇒⟨ μ₁ ⟩ τ₁'} c k t₂ = cons c k t₂

cons {μ₂ = ●} refl k tt = k
cons {.τ₁} {.τ₁'} {μ₁} {τ₂ ⇒⟨ μ₂ ⟩ τ₂'} {τ₁ ⇒⟨ μ₃ ⟩ τ₁'} (refl , refl , c) k k' =
  λ v → λ t' → k v (cons c k' t')

-- is0
is0 : ℕ → 𝔹
is0 zero    = true
is0 (suc _) = false

-- b2s
b2s : 𝔹 → String
b2s true = "true"
b2s false = "false"

-- Interpretation of values and expressions
cpsv : {τ : Ty} → Val[ 〚_〛τ  ] τ → 〚 τ 〛τ

cpsp : {τ : Ty} → PExp[ 〚_〛τ  ] τ → 〚 τ 〛τ

cpsi : {τ α β : Ty} {μα μβ : Tr} →
       IExp[ 〚_〛τ  ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
       (〚 τ 〛τ → 〚 μα 〛μ → 〚 α 〛τ) → 〚 μβ 〛μ → 〚 β 〛τ

cpsv (Var x) = x
cpsv (Num n) = n
cpsv (Bol b) = b
cpsv (Str s) = s
cpsv (PAbs f) = λ x → cpsp (f x)
cpsv (IAbs f) = λ x → cpsi (f x)

cpsp (Val v) = cpsv v
cpsp (PApp e₁ e₂) = (cpsp e₁) (cpsp e₂)
cpsp (PPlus e₁ e₂) = (cpsp e₁) + (cpsp e₂)
cpsp (PIs0 e) = is0 (cpsp e)
cpsp (PB2S e) = b2s (cpsp e)
cpsp (Prompt is-id e) =
  (cpsi e (kid is-id) tt)

cpsi (Exp e) k t = k (cpsp e) t

cpsi (PIApp e₁ e₂) k t =
  cpsi e₁
       (λ v₁ t₁ → cpsi e₂ (λ v₂ t₂ → k (v₁ v₂) t₂) t₁)
       t

cpsi (IApp e₁ e₂) k t =
  cpsi e₁
       (λ v₁ t₁ → cpsi e₂ (λ v₂ t₂ → v₁ v₂ k t₂) t₁)
       t

cpsi (IPlus e₁ e₂) k t =
  cpsi e₁
       (λ v₁ t₁ → cpsi e₂ (λ v₂ t₂ → k (v₁ + v₂) t₂) t₁)
       t

cpsi (IIs0 e) k t =
  cpsi e (λ v t' → k (is0 v) t') t

cpsi (IB2S e) k t =
  cpsi e (λ v t' → k (b2s v) t') t

cpsi (PControl is-id f) k t =
  cpsi (f λ v → k v t) (kid is-id) tt

cpsi (IControl is-id c₁ c₂ f) k t =
  cpsi (f (λ v k' t' → k v (append c₂ t (cons c₁ k' t'))))
       (kid is-id)
       tt

-- Top-level evaluation (proof of Theorem 8)
go : {τ : Ty} → PExp[ 〚_〛τ ] τ → 〚 τ 〛τ
go e = cpsp e


-- Examples and tests
-- ⟨ 12 ⟩
exp0 : {var : Ty → Set} → PExp[ var ] Nat
exp0 =
  Prompt refl (Exp (Val (Num 12)))

test0 : go exp0 ≡ 12
test0 = refl

-- ⟨ 12 + Fk. k 2 ⟩
exp1 : {var : Ty → Set} → PExp[ var ] Nat
exp1 =
  Prompt refl
          (IPlus (Exp (Val (Num 12)))
                 (PControl {τ = Nat}
                           refl
                           (λ k → Exp (PApp (Val (Var k)) (Val (Num 2))))))

test1 : go exp1 ≡ 14
test1 = refl

-- 1 + ⟨ 2 + Fk. k (k 3) ⟩
exp2 : {var : Ty → Set} → PExp[ var ] Nat
exp2 =
  PPlus (Val (Num 1))
        (Prompt refl
                 (IPlus (Exp (Val (Num 2)))
                        (PControl {τ = Nat}
                                  refl
                                   (λ k → Exp (PApp (Val (Var k))
                                              (PApp (Val (Var k)) (Val (Num 3))))))))

test2 : go exp2 ≡ 8
test2 = refl

-- Example adapted from Shan [HOSC 2007]
-- (yields different results if control is replaced by
-- shift, shift0, and control0)
-- ⟨ ⟨ 1 + ⟨ (λ x. Fh. x) (Ff. Fg. 2 + f 5) ⟩ ⟩ ⟩
exp3 : {var : Ty → Set} → PExp[ var ] Nat
exp3 =
  Prompt refl
    (Exp (Prompt refl
      (Exp (PPlus
        (Val (Num 1))
             (Prompt (refl , refl , refl)
                      (IApp (Exp (Val (IAbs (λ x →
                                   PControl refl
                                            (λ h → Exp (Val (Var x)))))))
                            (IControl {γ = Nat} refl refl refl
                                      (λ f →
                                        PControl refl
                                                 (λ g →
                                                    IPlus (Exp (Val (Num 2)))
                                                          (IApp (Exp (Val (Var f)))
                                                                (Exp (Val (Num 5)))))))))))))

test3 : go exp3 ≡ 6
test3 = refl

-- Motivating example from Section 2
-- ⟨ (Fk₁. is0 (k₁ 5)) + (Fk₂. b2s (k₂ 8)) ⟩
exp4 : {var : Ty → Set} → PExp[ var ] Str
exp4 =
  Prompt (refl , refl , refl)
          (IPlus (IControl refl refl refl
                           (λ k₁ → IIs0 (IApp (Exp (Val (Var k₁))) (Exp (Val (Num 5))))))
                 (PControl refl
                           (λ k₂ → Exp (PB2S (PApp (Val (Var k₂)) (Val (Num 8)))))))

test4 : go exp4 ≡ "false"
test4 = refl

{-
-- Non-terminating example from Kameyama and Yonezawa [FLOPS 2008]
-- (ill-typed in λF)
-- ⟨ (Fk₁. k₁ 1; k₁ 1); (Fk₂. k₂ 1; k₂ 1) ⟩
exp5 : {var : Ty → Set} → PExp[ var ] Nat
exp5 =
  Prompt {μᵢ = Nat ⇒⟨ ● ⟩ Nat} -- 1
          (refl , refl , refl)
          (IApp {μβ = Nat ⇒⟨ ● ⟩ Nat} -- 2
                (Exp (Val (IAbs (λ a →
                  IControl {μᵢ = ●} -- 3
                           {μ₀ = Nat ⇒⟨ ● ⟩ Nat} -- 4
                           {μ₁ = ●} -- 5
                           {μ₂ = ●} -- 6
                           {μα = Nat ⇒⟨ ● ⟩ Nat} -- 7
                           {μβ = Nat ⇒⟨ ● ⟩ Nat} -- 8
                           refl
                           refl
                           (refl , refl , {!!}) -- (Nat ⇒⟨ ● ⟩ Nat) ≡ ●
                           (λ k₂ → IApp (Exp (Val (IAbs (λ c → IApp (Exp (Val (Var k₂)))
                                                                   (Exp (Val (Num 1)))))))
                                        (IApp (Exp (Val (Var k₂))) (Exp (Val (Num 1)))))))))
                 (IControl {μᵢ = ●} -- 9
                           {μ₀ = Nat ⇒⟨ ● ⟩ Nat} -- 10
                           {μ₁ = ●} -- 11
                           {μ₂ = ●} -- 12
                           {μα = Nat ⇒⟨ ● ⟩ Nat} -- 13
                           {μβ = ●} -- 14
                           refl
                           refl
                           refl
                           (λ k₁ → IApp (Exp (Val (IAbs (λ b → IApp (Exp (Val (Var k₁)))
                                                                    (Exp (Val (Num 1)))))))
                                        (IApp (Exp (Val (Var k₁))) (Exp (Val (Num 1)))))))
-}

{-
Let eᵢ = kᵢ 1; kᵢ 1 where i = 1, 2.

a. By (IControl), initial trail type of eᵢ = ●.
   By (IApp), initial trail type of eᵢ = initial trail type of body of kᵢ.
   Therefore, 6 = 12 = ●.

b. By (IApp), final trail type of eᵢ = final trail type of body of kᵢ.
   Therefore, 3 = 5, 9 = 11.

c. By (IApp), final trail type of first kᵢ 1 = initial trail type of second kᵢ 1.
   Therefore, 5 = 6, 11 = 12.

d. By a, c, and compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₂) μ₂ μ₀, 4 = 10 = Nat ⇒⟨ ● ⟩ Nat

e. By (Prompt), initial trail type of body of prompt = ●.
   By (IApp), initial trail type of body of prompt = initial trail type of Fk₁. e₁.
   Therefore, 14 = ●.

f. By compatible μβ μ₀ μα, 13 = Nat ⇒⟨ ● ⟩ Nat.

g. By (IApp), final trail type of Fk₁. e₁ = initial trail type of Fk₂. e₂.
   Therefore, 8 = Nat ⇒⟨ ● ⟩ Nat.

h. By (Prompt), final trail type of body of prompt must satisfy id-cont-type.
   By (IApp), final trail type of body of prompt = final trail type of Fk₂. e₂.
   Therefore, 7 = Nat ⇒⟨ ● ⟩ Nat.

i. By d, g, and h, compatible μβ μ₀ μα does not hold for Fk₂. e₂.
-}


-- Encoding of shift
shift : {var : Ty → Set} {τ α β γ γ' : Ty} {μα μᵢ : Tr} →
        id-cont-type γ μᵢ γ' →
        PExp[ var ] ((τ ⇒p α) ⇒i γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) →
        IExp[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ β
shift p f =
  PControl p
    (λ k → IApp (Exp f)
                (Exp (Val (PAbs (λ x →
                  Prompt refl (Exp (PApp (Val (Var k)) (Val (Var x)))))))))

-- Shan's example
exp5 : {var : Ty → Set} → PExp[ var ] Nat
exp5 =
  Prompt refl (Exp
    (Prompt refl (Exp
      (PPlus
        (Val (Num 1))
             (Prompt {β = Nat} refl
                      (IApp (Exp (Val (IAbs (λ x →
                                   shift refl (Val (IAbs (λ h → Exp (Val (Var x)))))))))
                            (shift {γ = Nat} refl
                              (Val
                                (IAbs (λ f →
                                         shift refl
                                           (Val
                                             (IAbs
                                               (λ g → IPlus (Exp (Val (Num 2)))
                                                            (Exp (PApp (Val (Var f))
                                                                       (Val (Num 5)))))))))))))))))

test5 : go exp5 ≡ 8
test5 = refl
