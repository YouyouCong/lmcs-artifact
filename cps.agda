-- Formalization of λC & CPS translation of λF

module CPS where

open import LambdaF hiding (〚_〛τ; 〚_〛μ; cpsv; cpse; append; cons; kid)
open import Data.Nat using (ℕ)
open import Data.Bool renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

-- λC: Target calculus of CPS

-- Expression types
data CTy : Set where
  Nat  : CTy
  Bool : CTy
  Str  : CTy
  _⇒_  : CTy → CTy → CTy
  ●    : CTy

infixr 6 _⇒_

-- CPS translation of types
〚_〛τ : Ty → CTy
〚_〛μ : Tr → CTy

〚 Nat 〛τ = Nat
〚 Bool 〛τ = Bool
〚 Str 〛τ = Str
〚 τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β 〛τ =
  〚 τ₁ 〛τ ⇒ (〚 τ₂ 〛τ ⇒ 〚 μα 〛μ ⇒ 〚 α 〛τ) ⇒ 〚 μβ 〛μ ⇒ 〚 β 〛τ

〚 ● 〛μ = ●
〚 τ ⇒⟨ μ ⟩ τ' 〛μ = 〚 τ 〛τ ⇒ 〚 μ 〛μ ⇒ 〚 τ' 〛τ

-- Values and expressions
data CVal[_]_ (var : CTy → Set) : CTy → Set₁
data CExp[_]_ (var : CTy → Set) : CTy → Set₁

data CVal[_]_ var where
  Var : {τ : CTy} → var τ → CVal[ var ] τ 
  Num : ℕ → CVal[ var ] Nat 
  Bol : 𝔹 → CVal[ var ] Bool
  Str : String → CVal[ var ] Str 
  Abs : {τ₁ τ₂ : CTy} →
        (var τ₁ → CExp[ var ] τ₂) → CVal[ var ] (τ₁ ⇒ τ₂)
  Emp : CVal[ var ] ●

data CExp[_]_ var where
  Val  : {τ : CTy} →
         CVal[ var ] τ → CExp[ var ] τ
  App  : {τ₁ τ₂ : CTy} →
         CExp[ var ] (τ₁ ⇒ τ₂) → CExp[ var ] τ₁ → CExp[ var ] τ₂
  Plus : CExp[ var ] Nat → CExp[ var ] Nat → CExp[ var ] Nat
  Is0  : CExp[ var ] Nat → CExp[ var ] Bool
  B2S  : CExp[ var ] Bool → CExp[ var ] Str
  Case : {μ : Tr} {τ : CTy} →
         CExp[ var ] 〚 μ 〛μ →
         (μ ≡ ● → CExp[ var ] τ) →
         ({τ₁ τ₁' : Ty} {μ₁ : Tr} →
          μ ≡ τ₁ ⇒⟨ μ₁ ⟩ τ₁' → CExp[ var ] τ) →
         CExp[ var ] τ

-- For simplicity, we do not introduce a pattern variable
-- (k : 〚 μ 〛μ in rule (Case) in Figure 5) in the second clause
-- of case analysis.
-- This causes no loss of expressiveness; we can always directly
-- use the scrutinee.

-- Identity continuation
kid : {var : CTy → Set} {τ τ' : Ty} {μ : Tr} →
      id-cont-type τ μ τ' →
      CExp[ var ] (〚 τ 〛τ ⇒ 〚 μ 〛μ ⇒ 〚 τ' 〛τ)
kid {var} {τ} {τ'} {μ} i =
  Val (Abs (λ v → Val (Abs λ t →
    Case (Val (Var t))
         (λ p → let i' = subst (λ x → id-cont-type τ x τ') p i in
                let v' = subst (λ x → var 〚 x 〛τ) i' v in
                Val (Var v'))
         (λ {τ₁} {τ₁'} {μ₁} p → 
           let i' = subst (λ x → id-cont-type τ x τ') p i in
           let t' = subst (λ x →  var 〚 x 〛μ) p t in
           let t'' = subst (λ x → var (〚 τ₁ 〛τ ⇒ 〚 x 〛μ ⇒ 〚 τ₁' 〛τ)) ((proj₂ ∘ proj₂) i') t' in
           let v' = subst (λ x →  var 〚 x 〛τ) (proj₁ i') v in
           let r = App (App (Val (Var t'')) (Val (Var v'))) (Val Emp) in
           subst (λ x → CExp[ var ] 〚 x 〛τ) (sym ((proj₁ ∘ proj₂) i')) r))))

-- Trail composition
cons-cxt-lemma : {τ₁ τ₁' τ₂ τ₂' : Ty} {μ₁ μ₂ μ₃ : Tr} →
                 (c : compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') (τ₂ ⇒⟨ μ₂ ⟩ τ₂') μ₃) →
                 Σ[ μ₃' ∈ Tr ] (μ₃ ≡ τ₁ ⇒⟨ μ₃' ⟩ τ₁')
cons-cxt-lemma {μ₃ = τ₃ ⇒⟨ μ₃' ⟩ τ₃'} (refl , refl , c) = μ₃' , refl

append : {var : CTy → Set} {μ₁ μ₂ μ₃ : Tr} →
         compatible μ₁ μ₂ μ₃ →
         CExp[ var ] (〚 μ₁ 〛μ ⇒ 〚 μ₂ 〛μ ⇒ 〚 μ₃ 〛μ)

cons : {var : CTy → Set} {τ₁ τ₁' : Ty} {μ₁ μ₂ μ₃ : Tr} →
       compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') μ₂ μ₃ →
       CExp[ var ] (〚 τ₁ ⇒⟨ μ₁ ⟩ τ₁' 〛μ ⇒ 〚 μ₂ 〛μ ⇒ 〚 μ₃ 〛μ)
       
append {var} {μ₁} {μ₂} {μ₃} c = 
  Val (Abs (λ t₁ → Val (Abs (λ t₂ →
    Case (Val (Var t₁))
         (λ p → let c' = subst (λ x → compatible x μ₂ μ₃) p c in
                let t₂' = subst (λ x → var 〚 x 〛μ) c' t₂ in
                Val (Var t₂'))
         (λ {τ₁} {τ₁'} {μ₁'} p → 
            let c' = subst (λ x → compatible x μ₂ μ₃) p c in
            let t₁' = subst (λ x → var 〚 x 〛μ) p t₁ in
            App (App (cons c') (Val (Var t₁'))) (Val (Var t₂)))))))

{-# TERMINATING #-}
cons {var} {τ₁} {τ₁'} {μ₁} {μ₂} {μ₃} c = 
  Val (Abs (λ k → Val (Abs (λ t →
    Case (Val (Var t))
         (λ p → let c' = subst (λ x → compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') x μ₃) p c in
                let k' = subst (λ x → var 〚 x 〛μ) c' k in
                Val (Var k'))
         (λ {τ₂} {τ₂'} {μ₂'} p → 
            let c' = subst (λ x → compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') x μ₃) p c in
            let eq = proj₂ (cons-cxt-lemma c') in
            let c'' = subst (λ x → compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') (τ₂ ⇒⟨ μ₂' ⟩ τ₂') x) eq c' in
            let t' = subst (λ x → var 〚 x 〛μ) p t in
            subst (λ x → CExp[ var ] 〚 x 〛μ) (sym eq)
                  (Val (Abs (λ v → Val (Abs (λ t₁ →
                    App (App (Val (Var k)) (Val (Var v)))
                    (App (App (cons ((proj₂ ∘ proj₂) c''))
                              (Val (Var t')))
                         (Val (Var t₁)))))))))))))

-- The use of subst results in the failure of termination check,
-- but we can easily see that the size of input types decreases
-- on every three recursive calls.

-- CPS translation of values and expressions
-- (proof of Theorem 4)
cpsv : {var : CTy → Set} {τ : Ty} →
       Val[ var ∘ 〚_〛τ  ] τ → CVal[ var ] 〚 τ 〛τ
        
cpse : {var : CTy → Set} {τ α β : Ty} {μα μβ : Tr} →
       Exp[ var ∘ 〚_〛τ ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
       CVal[ var ] ((〚 τ 〛τ ⇒ 〚 μα 〛μ ⇒ 〚 α 〛τ) ⇒ 〚 μβ 〛μ ⇒ 〚 β 〛τ)

cpsv (Var x) = Var x
cpsv (Num n) = Num n
cpsv (Bol b) = Bol b
cpsv (Str s) = Str s
cpsv {var = var} (Abs f) = Abs (λ x → Val (cpse (f x)))

cpse (Val v) =
  Abs (λ k → Val (Abs (λ t →
    App (App (Val (Var k)) (Val (cpsv v))) (Val (Var t)))))
    
cpse (App e₁ e₂) =
  Abs (λ k → Val (Abs (λ t →
    App (App (Val (cpse e₁))
             (Val (Abs (λ v₁ → (Val (Abs (λ t₁ →
                    (App (App (Val (cpse e₂))
                              (Val (Abs (λ v₂ → Val (Abs (λ t₂ →
                                App (App (App (Val (Var v₁)) (Val (Var v₂)))
                                         (Val (Var k)))
                                    (Val (Var t₂))))))))
                         (Val (Var t₁))))))))))
        (Val (Var t)))))
        
cpse (Plus e₁ e₂) =
  Abs (λ k → Val (Abs (λ t →
    App (App (Val (cpse e₁))
             (Val (Abs (λ v₁ → (Val (Abs (λ t₁ →
                    App (App (Val (cpse e₂))
                             (Val (Abs (λ v₂ → Val (Abs (λ t₂ →
                               App (App (Val (Var k))
                                        (Plus (Val (Var v₁)) (Val (Var v₂))))
                                    (Val (Var t₂))))))))
                        (Val (Var t₁)))))))))
        (Val (Var t)))))
        
cpse (Is0 e) =
  Abs (λ k → Val (Abs (λ t →
    App (App (Val (cpse e))
             (Val (Abs (λ v → (Val (Abs (λ t' →
                  App (App (Val (Var k))
                           (Is0 (Val (Var v))))
                      (Val (Var t')))))))))
        (Val (Var t)))))
        
cpse (B2S e) =
  Abs (λ k → Val (Abs (λ t →
    App (App (Val (cpse e))
             (Val (Abs (λ v → (Val (Abs (λ t' →
                  App (App (Val (Var k))
                           (B2S (Val (Var v))))
                      (Val (Var t')))))))))
        (Val (Var t)))))

cpse (Control id c₁ c₂ f) =
  Abs (λ k → Val (Abs (λ t →
    App (Val (Abs (λ x → App (App (Val (cpse (f x))) (kid id))
                             (Val Emp))))
        (Val (Abs (λ v → Val (Abs (λ k' → Val (Abs (λ t' →
          App (App (Val (Var k)) (Val (Var v)))
              (App (App (append c₂) (Val (Var t)))
                   (App (App (cons c₁) (Val (Var k')))
                        (Val (Var t'))))))))))))))

cpse (Prompt id e) =
  Abs (λ k → Val (Abs (λ t →
    App (App (Val (Var k))
             (App (App (Val (cpse e)) (kid id))
                  (Val Emp)))
        (Val (Var t)))))

