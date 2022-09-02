-- Formalization of λF

module LambdaF where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality

-- Expression and trail types
data Ty : Set
data Tr : Set

data Ty where
  Nat         : Ty
  Bool        : Ty
  Str         : Ty
  _⇒_⟨_⟩_⟨_⟩_ : Ty → Ty → Tr → Ty → Tr → Ty → Ty

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
data Exp[_]_⟨_⟩_⟨_⟩_ (var : Ty → Set) : Ty → Tr → Ty → Tr → Ty → Set

data Val[_]_ var where
  Var     : {τ : Ty} → var τ → Val[ var ] τ 
  Num     : ℕ → Val[ var ] Nat 
  Bol     : 𝔹 → Val[ var ] Bool
  Str     : String → Val[ var ] Str 
  Abs     : {τ₁ τ₂ α β : Ty} {μα μβ : Tr} →
            (var τ₁ → Exp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            Val[ var ] (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) 

data Exp[_]_⟨_⟩_⟨_⟩_ var where
  Val     : {τ α : Ty} {μ : Tr} →
            Val[ var ] τ → Exp[ var ] τ ⟨ μ ⟩ α ⟨ μ ⟩ α
  App     : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
            Exp[ var ] (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ →
            Exp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ →
            Exp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μδ ⟩ δ
  Plus    : {α β γ : Ty} {μα μβ μγ : Tr} →
            Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            Exp[ var ] Nat ⟨ μγ ⟩ γ ⟨ μα ⟩ α →
            Exp[ var ] Nat ⟨ μγ ⟩ γ ⟨ μβ ⟩ β
  Is0     : {α β : Ty} {μα μβ : Tr} →
            Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            Exp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β
  B2S     : {α β : Ty} {μα μβ : Tr} →
            Exp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            Exp[ var ] Str ⟨ μα ⟩ α ⟨ μβ ⟩ β
  Control : {τ α β γ γ' τ₁ τ₁' : Ty} {μᵢ μ₀ μ₁ μ₂ μα μβ : Tr} →
            id-cont-type γ μᵢ γ' →
            compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') μ₂ μ₀ →
            compatible μβ μ₀ μα →
            (var (τ ⇒ τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α) →
             Exp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) →
            Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β
  Prompt  : {τ α β β' : Ty} {μᵢ μα : Tr} →
            id-cont-type β μᵢ β' →
            Exp[ var ] β ⟨ μᵢ ⟩ β' ⟨ ● ⟩ τ →
            Exp[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ α


-- CPS interpreter

-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛μ : Tr → Set

〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 Str 〛τ = String
〚 τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β 〛τ =
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
cpsv :  {τ : Ty} → Val[ 〚_〛τ  ] τ → 〚 τ 〛τ 

cpse : {τ α β : Ty} {μα μβ : Tr} →
        Exp[ 〚_〛τ  ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
        (〚 τ 〛τ → 〚 μα 〛μ → 〚 α 〛τ) → 〚 μβ 〛μ → 〚 β 〛τ

cpsv (Var x) = x
cpsv (Num n) = n
cpsv (Bol b) = b
cpsv (Str s) = s
cpsv (Abs f) = λ x → cpse (f x)

cpse (Val v) k t = k (cpsv v) t

cpse (App e₁ e₂) k t =
  cpse e₁
       (λ v₁ t₁ → cpse e₂ (λ v₂ t₂ → v₁ v₂ k t₂) t₁)
       t
    
cpse (Plus e₁ e₂) k t =
  cpse e₁
       (λ v₁ t₁ → cpse e₂ (λ v₂ t₂ → k (v₁ + v₂) t₂) t₁)
       t
    
cpse (Is0 e) k t =
  cpse e (λ v t' → k (is0 v) t') t
  
cpse (B2S e) k t =
  cpse e (λ v t' → k (b2s v) t') t
  
cpse (Control is-id c₁ c₂ f) k t =
  cpse (f (λ v k' t' → k v (append c₂ t (cons c₁ k' t'))))
       (kid is-id)
       tt
       
cpse (Prompt is-id e) k t =
  k (cpse e (kid is-id) tt) t

-- Top-level evaluation (partial proof of Conjecture 1)
go : {τ : Ty} → Exp[ 〚_〛τ ] τ ⟨ ● ⟩ τ ⟨ ● ⟩ τ → 〚 τ 〛τ
go e = cpse e (λ z _ → z) tt


-- Examples and tests
-- ⟨ 12 ⟩
exp0 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp0 =
  Prompt refl (Val (Num 12))

test0 : go exp0 ≡ 12
test0 = refl

-- ⟨ 12 + Fk. k 2 ⟩
exp1 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp1 =
  Prompt (refl , refl , refl)
         (Plus (Val (Num 12))
               (Control {τ = Nat} 
                        refl refl refl
                        (λ k → App (Val (Var k)) (Val (Num 2)))))

test1 : go exp1 ≡ 14
test1 = refl

-- 1 + ⟨ 2 + Fk. k (k 3) ⟩
exp2 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp2 =
  Plus (Val (Num 1))
       (Prompt (refl , refl , refl)
               (Plus (Val (Num 2))
                     (Control {τ = Nat}
                              refl refl refl
                              (λ k → App (Val (Var k))
                                         (App (Val (Var k)) (Val (Num 3)))))))

test2 : go exp2 ≡ 8
test2 = refl

-- Example adapted from Shan [HOSC 2007]
-- (yields different results if control is replaced by
-- shift, shift0, and control0)
-- ⟨ ⟨ 1 + ⟨ (λ x. Fh. x) (Ff. Fg. 2 + f 5) ⟩ ⟩ ⟩
exp3 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp3 =
  Prompt refl
    (Prompt refl
      (Plus (Val (Num 1))
         (Prompt {β' = Nat} (refl , refl , refl)
                 (App (Val (Abs (λ x →
                              Control {τ₁ = Nat} {τ₁' = Nat} {μ₁ = ●} {μ₂ = ●}
                                      refl refl (refl , refl , refl)
                                      (λ h → Val (Var x)))))
                       (Control {γ = Nat} (refl , refl , refl) refl refl
                                (λ f →
                                   Control {τ₁ = Nat} {τ₁' = Nat} {μ₁ = ●} {μ₂ = ●}
                                           (refl , refl , refl) refl refl
                                           (λ g →
                                              Plus (Val (Num 2))
                                                   (App (Val (Var f)) (Val (Num 5))))))))))
                                                                
test3 : go exp3 ≡ 6
test3 = refl

-- Example (2) from Section 2
-- ⟨ (Fk₁. is0 (k₁ 5)) + (Fk₂. b2s (k₂ 8)) ⟩
exp4 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Str ⟨ μα ⟩ α ⟨ μα ⟩ α
exp4 =
  Prompt {β = Nat} {β' = Str} {μᵢ = Nat ⇒⟨ ● ⟩ Str}
         (refl , refl , refl)
         (Plus (Control {α = Str}
                        {β = Str}
                        {μᵢ = Bool ⇒⟨ ● ⟩ Str}
                        {μ₀ = Nat ⇒⟨ Bool ⇒⟨ ● ⟩ Str ⟩ Str}
                        {μ₁ = Bool ⇒⟨ ● ⟩ Str}
                        {μ₂ = ●}
                        {μα = Nat ⇒⟨ Bool ⇒⟨ ● ⟩ Str ⟩ Str}
                        {μβ = ●}
                        (refl , refl , refl) refl refl
                        (λ k₁ → Is0 (App (Val (Var k₁)) (Val (Num 5)))))
               (Control {α = Str}
                        {β = Str}
                        {μᵢ = ●}
                        {μ₀ = Bool ⇒⟨ ● ⟩ Str}
                        {μ₁ = ●}
                        {μ₂ = ●}
                        {μα = Nat ⇒⟨ ● ⟩ Str}
                        {μβ = Nat ⇒⟨ Bool ⇒⟨ ● ⟩ Str ⟩ Str}
                        refl refl (refl , refl , refl)
                        (λ k₂ → B2S (App (Val (Var k₂)) (Val (Num 8))))))

test4 : go exp4 ≡ "false"
test4 = refl

{-
-- Non-terminating example from Kameyama and Yonezawa [FLOPS 2008]
-- (ill-typed in λF)
-- ⟨ (Fk₁. k₁ 1; k₁ 1); (Fk₂. k₂ 1; k₂ 1) ⟩
exp5 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp5 =
  Prompt {μᵢ = Nat ⇒⟨ ● ⟩ Nat} -- 1
         (refl , refl , refl)
         (App {μβ = Nat ⇒⟨ ● ⟩ Nat} -- 2
              (Val (Abs (λ a →
                Control {μᵢ = ●} -- 3
                        {μ₀ = Nat ⇒⟨ ● ⟩ Nat} -- 4
                        {μ₁ = ●} -- 5
                        {μ₂ = ●} -- 6
                        {μα = Nat ⇒⟨ ● ⟩ Nat} -- 7
                        {μβ = Nat ⇒⟨ ● ⟩ Nat} -- 8
                        refl
                        refl
                        (refl , refl , {!!}) -- (Nat ⇒⟨ ● ⟩ Nat) ≡ ●
                        (λ k₂ → App (Val (Abs (λ c → App (Val (Var k₂)) (Val (Num 1)))))
                                    (App (Val (Var k₂)) (Val (Num 1)))))))
              (Control {μᵢ = ●} -- 9
                       {μ₀ = Nat ⇒⟨ ● ⟩ Nat} -- 10
                       {μ₁ = ●} -- 11
                       {μ₂ = ●} -- 12
                       {μα = Nat ⇒⟨ ● ⟩ Nat} -- 13
                       {μβ = ●} -- 14
                       refl
                       refl
                       refl
                       (λ k₁ → App (Val (Abs (λ b → App (Val (Var k₁)) (Val (Num 1)))))
                                   (App (Val (Var k₁)) (Val (Num 1))))))
-}

{-
Let eᵢ = kᵢ 1; kᵢ 1 where i = 1, 2.

a. By (Control), initial trail type of eᵢ = ●.
   By (App), initial trail type of eᵢ = initial trail type of body of kᵢ.
   Therefore, 6 = 12 = ●.

b. By (App), final trail type of eᵢ = final trail type of body of kᵢ.
   Therefore, 3 = 5, 9 = 11.

c. By (App), final trail type of first kᵢ 1 = initial trail type of second kᵢ 1.
   Therefore, 5 = 6, 11 = 12.

d. By a, c, and compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₂) μ₂ μ₀, 4 = 10 = Nat ⇒⟨ ● ⟩ Nat

e. By (Prompt), initial trail type of body of prompt = ●.
   By (App), initial trail type of body of prompt = initial trail type of Fk₁. e₁.
   Therefore, 14 = ●.

f. By compatible μβ μ₀ μα, 13 = Nat ⇒⟨ ● ⟩ Nat.

eg. By (App), final trail type of Fk₁. e₁ = initial trail type of Fk₂. e₂.
r   Therefore, 8 = Nat ⇒⟨ ● ⟩ Nat.

h. By (Prompt), final trail type of body of prompt must satisfy id-cont-type.
   By (App), final trail type of body of prompt = final trail type of Fk₂. e₂.
   Therefore, 7 = Nat ⇒⟨ ● ⟩ Nat.

i. By d, g, and h, compatible μβ μ₀ μα does not hold for Fk₂. e₂.
-}

-- Encoding of shift
shift : {var : Ty → Set} {τ α β γ γ' : Ty} {μ₀ μᵢ μα : Tr} →
        id-cont-type γ μᵢ γ' →
        compatible (α ⇒⟨ ● ⟩ α) ● μ₀ →
        compatible μα μ₀ μα →
        Exp[ var ] ((τ ⇒ α ⟨ ● ⟩ α ⟨ ● ⟩ α) ⇒ γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) ⟨ ● ⟩ β ⟨ ● ⟩ β →
        Exp[ var ] τ ⟨ μα ⟩ α ⟨ μα ⟩ β
shift {α = α} id c₁ c₂ f =
  Control {τ₁ = α} id c₁ c₂
    (λ k → App f (Val (Abs (λ x → Prompt refl (App (Val (Var k)) (Val (Var x)))))))

{-
initial trail of body of control = initial trail of f = ● 
initial trail of body of prompt = initial trail of body of k = ●
answer type of < k x > = type of k x = α
final answer type of shift = final answer type of f = β
-}

{-
compatible (α ⇒⟨ ● ⟩ α) ● μ₀ means μ₀ ≡ α ⇒⟨ ● ⟩ α.
Hence we need compatible μα (α ⇒⟨ ● ⟩ α) μα,
which says μα does not change when composed with the future context.
This cannot hold as shown by c below.
-}

c : {α : Ty} {μα : Tr} → compatible μα (α ⇒⟨ ● ⟩ α) μα → ⊥
c {μα = ●} ()
c {μα = τ₁ ⇒⟨ ● ⟩ τ₁'} ()
c {μα = τ₁ ⇒⟨ τ₂ ⇒⟨ ● ⟩ .τ₂ ⟩ τ₁'} (refl , refl , refl , refl , ())
c {μα = τ₁ ⇒⟨ τ₂ ⇒⟨ τ₃ ⇒⟨ μ₂ ⟩ τ₃' ⟩ .τ₂ ⟩ τ₁'}
  (refl , refl , refl , refl , ())

{-
As we can never supply the proof of the second compatibility relation,
we can never use shift in programs.
-}

{-
-- ⟨ shift k. k 42 ⟩
exp6 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp6 =
  Prompt refl
         (shift refl refl {!!} -- (Nat ⇒⟨ ● ⟩ Nat) ≡ ●
         (Val (Abs (λ k → App (Val (Var k)) (Val (Num 42))))))

-- Shan's example
-- ⟨ ⟨ 1 + ⟨ (λ x. Sh. x) (Sf. Sg. 2 + f 5) ⟩ ⟩ ⟩
exp7 : {var : Ty → Set} {α : Ty} {μα : Tr} →
       Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μα ⟩ α
exp7 =
  Prompt refl
    (Prompt refl
      (Plus
        (Val (Num 1))
             (Prompt {β = Nat} refl
                     (App (Val (Abs (λ x →
                                 shift refl refl {!!} -- (Nat ⇒⟨ ● ⟩ Nat) ≡ ●
                                       (Val (Abs (λ h → Val (Var x)))))))
                          (shift {γ = Nat} refl refl {!!} -- (Nat ⇒⟨ ● ⟩ Nat) ≡ ●
                            (Val
                              (Abs (λ f →
                                     shift refl refl {!!} -- (Nat ⇒⟨ ● ⟩ Nat) ≡ ●
                                           (Val
                                             (Abs
                                               (λ g → Plus (Val (Num 2))
                                                           (App (Val (Var f))
                                                                     (Val (Num 5))))))))))))))
-}
