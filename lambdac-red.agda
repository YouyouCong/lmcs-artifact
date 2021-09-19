-- Reduction of λC

module LambdaC-Red where

open import LambdaF hiding (〚_〛τ; 〚_〛μ)
open import CPS
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

-- Substitution
data SubstVal {var : CTy → Set} : {τ₁ τ₂ : CTy} →
              (var τ₁ → CVal[ var ] τ₂) →
              CVal[ var ] τ₁ →
              CVal[ var ] τ₂ → Set₁
               
data Subst {var : CTy → Set} : {τ₁ τ₂ : CTy} →
           (var τ₁ → CExp[ var ] τ₂) → CVal[ var ] τ₁ →
           CExp[ var ] τ₂ → Set₁

data SubstVal {var} where
  sVar= : {τ : CTy} {v : CVal[ var ] τ} →
          SubstVal (λ x → Var x) v v

  sVar≠ : {τ₁ τ₂ : CTy}
          {v : CVal[ var ] τ₂} {x : var τ₁} →
          SubstVal (λ y → Var x) v (Var x)

  sNum  : {τ : CTy} {n : ℕ}
          {v : CVal[ var ] τ} →
          SubstVal (λ x → Num n) v (Num n)

  sBol  : {τ : CTy} {b : 𝔹}
          {v : CVal[ var ] τ} →
          SubstVal (λ x → Bol b) v (Bol b)

  sStr  : {τ : CTy} {s : String}
          {v : CVal[ var ] τ} →
          SubstVal (λ x → Str s) v (Str s)

  sAbs  : {τ τ₁ τ₂ : CTy}
          {e : var τ₁ → var τ → CExp[ var ] τ₂} →
          {v : CVal[ var ] τ₁} →
          {e' : var τ → CExp[ var ] τ₂} →
          ((x : var τ) → Subst (λ y → (e y) x) v (e' x)) →
          SubstVal (λ y → Abs (e y)) v (Abs e')

  sEmp  : {τ : CTy} {v : CVal[ var ] τ} →
          SubstVal (λ x → Emp) v Emp

data Subst {var} where
  sVal  : {τ τ₁ : CTy}
          {v₁ : var τ → CVal[ var ] τ₁}
          {v : CVal[ var ] τ}
          {v₁' : CVal[ var ] τ₁} →
          SubstVal v₁ v v₁' →
          Subst (λ y → Val (v₁ y)) v (Val v₁')

  sApp  : {τ τ₁ τ₂ : CTy}
          {e₁ : var τ → CExp[ var ] (τ₁ ⇒ τ₂)}
          {e₂ : var τ → CExp[ var ] τ₁}
          {v : CVal[ var ] τ}
          {e₁' : CExp[ var ] (τ₁ ⇒ τ₂)}
          {e₂' : CExp[ var ] τ₁} →
          Subst e₁ v e₁' → Subst e₂ v e₂' →
          Subst (λ y → App (e₁ y) (e₂ y)) v (App e₁' e₂')

  sPlu : {τ : CTy} 
         {e₁ : var τ → CExp[ var ] Nat}
         {e₂ : var τ → CExp[ var ] Nat}
         {v : CVal[ var ] τ}
         {e₁' : CExp[ var ] Nat}
         {e₂' : CExp[ var ] Nat} →
         Subst e₁ v e₁' → Subst e₂ v e₂' →
         Subst (λ y → Plus (e₁ y) (e₂ y)) v (Plus e₁' e₂')

  sIs0 : {τ : CTy}
         {e : var τ → CExp[ var ] Nat}
         {v : CVal[ var ] τ}
         {e' : CExp[ var ] Nat} →
         Subst e v e' → 
         Subst (λ y → Is0 (e y)) v (Is0 e')

  sB2S : {τ : CTy}
         {e : var τ → CExp[ var ] Bool}
         {v : CVal[ var ] τ}
         {e' : CExp[ var ] Bool} →
         Subst e v e' → 
         Subst (λ y → B2S (e y)) v (B2S e')

  sCase : {μ : Tr} {τ τ₂ : CTy}
          {t : var τ → CExp[ var ] 〚 μ 〛μ}
          {e₁ : var τ → μ ≡ ● → CExp[ var ] τ₂}
          {e₂ : var τ → {τ₁ τ₁' : Ty} {μ₁' : Tr} →
                μ ≡ τ₁ ⇒⟨ μ₁' ⟩ τ₁' → CExp[ var ] τ₂}
          {v : CVal[ var ] τ}
          {t' : CExp[ var ] 〚 μ 〛μ}
          {e₁' : μ ≡ ● → CExp[ var ] τ₂}
          {e₂' : {τ₁ τ₁' : Ty} {μ₁' : Tr} →
                 μ ≡ τ₁ ⇒⟨ μ₁' ⟩ τ₁' → CExp[ var ] τ₂} →
          Subst t v t' →
          ((q : μ ≡ ●) → Subst (λ y → (e₁ y) q) v (e₁' q)) →
          ({τ₁ τ₁' : Ty} {μ₁' : Tr} →
           (q : μ ≡ τ₁ ⇒⟨ μ₁' ⟩ τ₁') → Subst (λ y → (e₂ y) q) v (e₂' q)) →
          Subst (λ y → Case (t y) (e₁ y) (e₂ y)) v
                (Case t' e₁' e₂')

-- Frames
data CFr[_] (var : CTy → Set) : CTy → CTy → Set₁ where
  App₁  : {τ₁ τ₂ : CTy} →
          (e₂ : CExp[ var ] τ₁) → CFr[ var ] (τ₁ ⇒ τ₂) τ₂
  App₂  : {τ₁ τ₂ : CTy} →
          (v₁ : CVal[ var ] (τ₁ ⇒ τ₂)) → CFr[ var ] τ₁ τ₂
  Is0   : CFr[ var ] Nat Bool
  B2S   : CFr[ var ] Bool Str
  Case : {μ : Tr} {τ : CTy} →
         (μ ≡ ● → CExp[ var ] τ) →
         ({τ₁ τ₁' : Ty} {μ₁ : Tr} →
          μ ≡ τ₁ ⇒⟨ μ₁ ⟩ τ₁' → CExp[ var ] τ) →
         CFr[ var ] 〚 μ 〛μ  τ

Fr-plug : {var : CTy → Set} {τ₁ τ₂ : CTy} →
          CFr[ var ] τ₁ τ₂ → CExp[ var ] τ₁ → CExp[ var ] τ₂
Fr-plug (App₁ e₂) e = App e e₂
Fr-plug (App₂ v₁) e = App (Val v₁) e
Fr-plug Is0 e = Is0 e
Fr-plug B2S e = B2S e
Fr-plug (Case e₁ e₂) e = Case e e₁ e₂

-- Evaluation contexts
data CCxt[_] (var : CTy → Set) : CTy → CTy → Set₁ where
  Hole : {τ : CTy} → CCxt[ var ] τ τ
  Fr   : {τ₁ τ₂ τ₃ : CTy} →
         CFr[ var ] τ₂ τ₃ → CCxt[ var ] τ₁ τ₂ →
         CCxt[ var ] τ₁ τ₃

Cxt-plug : {var : CTy → Set} {τ₁ τ₂ : CTy} →
           CCxt[ var ] τ₁ τ₂ → CExp[ var ] τ₁ → CExp[ var ] τ₂
Cxt-plug Hole e = e
Cxt-plug (Fr f c) e = Fr-plug f (Cxt-plug c e)

-- One-step reduction
data Reduce {var : CTy → Set} :
            {τ : CTy} →
            CExp[ var ] τ → CExp[ var ] τ → Set₁ where

  RBeta    : {τ τ₁ : CTy} →
             {e : var τ → CExp[ var ] τ₁} →
             {v : CVal[ var ] τ} →
             {e' : CExp[ var ] τ₁} →
             Subst e v e' →
             Reduce (App (Val (Abs e)) (Val v)) e'

  RPlus    : {n₁ n₂ : ℕ} →
             Reduce (Plus (Val (Num n₁)) (Val (Num n₂))) (Val (Num (n₁ + n₂)))

  RIs0     : {n : ℕ} →
             Reduce (Is0 (Val (Num n))) (Val (Bol (is0 n)))
 
  RB2S     : {b : 𝔹} →
             Reduce (B2S (Val (Bol b))) (Val (Str (b2s b)))

  RCaseEmp : {τ : CTy} →
             (e₁ : ● ≡ ● → CExp[ var ] τ) →
             (e₂ : {τ₁ τ₁' : Ty} {μ₁ : Tr} →
                   ● ≡ τ₁ ⇒⟨ μ₁ ⟩ τ₁' → CExp[ var ] τ) →
             Reduce (Case (Val Emp) e₁ e₂) (e₁ refl)

  RCaseCxt : {τ τ' : Ty} {μ : Tr} {τ₂ : CTy} 
             {k : CVal[ var ] (〚 τ 〛τ ⇒ 〚 μ 〛μ ⇒ 〚 τ' 〛τ)} →
             (e₁ : τ ⇒⟨ μ ⟩ τ' ≡ ● → CExp[ var ] τ₂) →
             (e₂ : {τ₁ τ₁' : Ty} {μ₁ : Tr} →
                   τ ⇒⟨ μ ⟩ τ' ≡ τ₁ ⇒⟨ μ₁ ⟩ τ₁' → CExp[ var ] τ₂) →
             Reduce (Case (Val k) e₁ e₂) (e₂ refl)

  RFr      : {τ₁ τ₂ : CTy} (e e' : CExp[ var ] τ₁)
             (f : CFr[ var ] τ₁ τ₂) →
             Reduce e e' →
             Reduce (Fr-plug f e) (Fr-plug f e')

  -- Multi-step reduction
  R*Id     : {τ : CTy} {e : CExp[ var ] τ} →
             Reduce e e

  R*Trans  : {τ : CTy} →
             (e₁ e₂ e₃ : CExp[ var ] τ) →
             Reduce e₁ e₂ → Reduce e₂ e₃ →
             Reduce e₁ e₃
