-- Reduction of λF

module LambdaF-Red where

open import LambdaF
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

-- Substitution
data SubstVal {var : Ty → Set} : {τ₁ τ₂ : Ty} →
              (var τ₁ → Val[ var ] τ₂) →
              Val[ var ] τ₁ →
              Val[ var ] τ₂ → Set 
              
data Subst {var : Ty → Set} : {τ₁ τ₂ τ₃ τ₄ : Ty} {μα μβ : Tr} →
           (var τ₁ → Exp[ var ] τ₂ ⟨ μα ⟩ τ₃ ⟨ μβ ⟩ τ₄) →
           Val[ var ] τ₁ →
           Exp[ var ] τ₂ ⟨ μα ⟩ τ₃ ⟨ μβ ⟩ τ₄ → Set 

data SubstVal {var} where
  sVar= : {τ : Ty} {v : Val[ var ] τ} →
          SubstVal (λ x → Var x) v v

  sVar≠ : {τ₁ τ₂ : Ty} {v : Val[ var ] τ₂} {x : var τ₁} →
          SubstVal (λ y → Var x) v (Var x)

  sNum  : {τ : Ty} {n : ℕ}
          {v : Val[ var ] τ} →
          SubstVal (λ x → Num n) v (Num n)

  sBol  : {τ : Ty} {b : 𝔹}
          {v : Val[ var ] τ} →
          SubstVal (λ x → Bol b) v (Bol b)

  sStr  : {τ : Ty} {s : String}
          {v : Val[ var ] τ} →
          SubstVal (λ x → Str s) v (Str s)

  sAbs  : {τ τ₁ τ₂ α β γ : Ty} {μα μβ : Tr}
          {e : var τ₁ → var τ → Exp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β}
          {v : Val[ var ] τ₁}
          {e' : var τ → Exp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
          ((x : var τ) → Subst (λ y → (e y) x) v (e' x)) →
          SubstVal (λ y → Abs (e y)) v (Abs e')

data Subst {var} where
  sVal  : {τ τ₁ τ₃ : Ty} {μα : Tr}
          {v₁ : var τ → Val[ var ] τ₁}
          {v : Val[ var ] τ}
          {v₁' : Val[ var ] τ₁} →
          SubstVal v₁ v v₁' →
          Subst {τ₃ = τ₃} {μα = μα} (λ y → Val (v₁ y)) v (Val v₁')

  sApp  : {τ τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr}
          {e₁ : var τ → Exp[ var ] (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ}
          {e₂ : var τ → Exp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ}
          {v : Val[ var ] τ}
          {e₁' : Exp[ var ] (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ}
          {e₂' : Exp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ} →
          Subst e₁ v e₁' → Subst e₂ v e₂' →
          Subst (λ y → App (e₁ y) (e₂ y)) v (App e₁' e₂')

  sPlu : {τ α β γ : Ty} {μα μβ μγ : Tr}
         {e₁ : var τ → Exp[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ}
         {e₂ : var τ → Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β}
         {v : Val[ var ] τ}
         {e₁' : Exp[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ }
         {e₂' : Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β  } →
         Subst e₁ v e₁' → Subst e₂ v e₂' →
         Subst (λ y → Plus (e₁ y) (e₂ y)) v (Plus e₁' e₂')

  sIs0 : {τ α β : Ty} {μα μβ : Tr}
         {e : var τ → Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β}
         {v : Val[ var ] τ}
         {e' : Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β  } →
         Subst e v e' → 
         Subst (λ y → Is0 (e y)) v (Is0 e')

  sB2S : {τ α β : Ty} {μα μβ : Tr}
         {e : var τ → Exp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β}
         {v : Val[ var ] τ}
         {e' : Exp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
         Subst e v e' → 
         Subst (λ y → B2S (e y)) v (B2S e')

  sCon : {τ τ₁ τ₁' τ₃ α β γ γ' : Ty} {μ₀ μ₁ μ₂ μᵢ μα μβ : Tr} →
         {e : var τ₃ →
              var (τ ⇒ τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α) →
              Exp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β}
         {v : Val[ var ] τ₃}
         {e' : var (τ ⇒ τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α) →
               Exp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β}
         {x₁ : id-cont-type γ μᵢ γ'}
         {x₂ : compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') μ₂ μ₀}
         {x₃ : compatible  μβ μ₀ μα} →
         ((k : var (τ ⇒ τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α)) →
               Subst (λ y → (e y) k) v ((e' k))) →
         Subst (λ y → Control x₁ x₂ x₃ (e y))
               v
               (Control x₁ x₂ x₃ e')

  sPro : {τ τ₃ β β' γ : Ty} {μᵢ μα : Tr}
         {e : var τ → Exp[ var ] β ⟨ μᵢ ⟩ β' ⟨ ● ⟩ γ}
         {v : Val[ var ] τ}
         {e' : Exp[ var ] β ⟨ μᵢ ⟩ β' ⟨ ● ⟩ γ}
         {x : id-cont-type β μᵢ β'} →
         Subst e v e' →
         Subst {τ₃ = τ₃} {μα = μα} (λ y → Prompt x (e y)) v
               (Prompt x e')
               

-- Frames
data Fr[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : Ty → Set)
       : Ty → Tr → Ty → Tr → Ty → Ty → Tr → Ty → Tr → Ty → Set where

  App₁  : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
          (e₂ : Exp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
          Fr[ var , (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ ]
            τ₂ ⟨ μα ⟩ α ⟨ μδ ⟩ δ

  App₂  : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
          (v₁ : Val[ var ] (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β)) →
          Fr[ var , τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ]
            τ₂ ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  Plus₁ : {α β γ : Ty} {μα μβ μγ : Tr} →
          (e₂ : Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
          Fr[ var , Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  Plus₂ : {α γ : Ty} {μα μγ : Tr} →
          (v₁ : Val[ var ] Nat) →
          Fr[ var , Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  Is0   : {α β : Ty} {μα μβ : Tr} →
          Fr[ var , Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β

  B2S   : {α β : Ty} {μα μβ : Tr} →
          Fr[ var , Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Str ⟨ μα ⟩ α ⟨ μβ ⟩ β
            
  Pro   : {τ α β β' : Ty} {μᵢ μα : Tr} →
          (id-cont-type β μᵢ β') →
          Fr[ var , β ⟨ μᵢ ⟩ β' ⟨ ● ⟩ τ ] τ ⟨ μα ⟩ α ⟨ μα ⟩ α

Fr-plug : {var : Ty → Set}
          {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : Ty} {μα μβ μγ μδ : Tr} →
          Fr[ var , τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆ →
          Exp[ var ] τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ →
          Exp[ var ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆

Fr-plug (App₁ e₂) e₁ = App e₁ e₂
Fr-plug (App₂ v₁) e₂ = App (Val v₁) e₂
Fr-plug (Plus₁ e₂) e₁ = Plus e₁ e₂
Fr-plug (Plus₂ v₁) e₂ = Plus (Val v₁) e₂
Fr-plug Is0 e = Is0 e
Fr-plug B2S e = B2S e
Fr-plug {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {μα = μα} {μγ = μγ} (Pro x) e =
  Prompt x e

-- Pure frames
data pFr[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : Ty → Set)
       : Ty → Tr → Ty → Tr → Ty → Ty → Tr → Ty → Tr → Ty → Set where
  App₁ : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
         (e₂ : Exp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
         pFr[ var , (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ ]
            τ₂ ⟨ μα ⟩ α ⟨ μδ ⟩ δ

  App₂ : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
         (v₁ : Val[ var ] (τ₁ ⇒ τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β)) →
         pFr[ var , τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ]
            τ₂ ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  Plus₁ : {α β γ : Ty} {μα μβ μγ : Tr} →
          (e₂ : Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
          pFr[ var , Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  Plus₂ : {α γ : Ty} {μα μγ : Tr} →
          (v₁ : Val[ var ] Nat) →
          pFr[ var , Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  Is0   : {α β : Ty} {μα μβ : Tr} →
          pFr[ var , Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β
  B2S   : {α β : Ty} {μα μβ : Tr} →
          pFr[ var , Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Str ⟨ μα ⟩ α ⟨ μβ ⟩ β
       
pFr-plug : {var : Ty → Set}
           {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : Ty} {μα μβ μγ μδ : Tr} →
           pFr[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
           Exp[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
           Exp[ var ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆

pFr-plug (App₁ e₂) e₁ = App e₁ e₂
pFr-plug (App₂ v₁) e₂ = App (Val v₁) e₂
pFr-plug (Plus₁ e₂) e₁ = Plus e₁ e₂
pFr-plug (Plus₂ v₁) e₂ = Plus (Val v₁) e₂
pFr-plug Is0 e = Is0 e
pFr-plug B2S e = B2S e

data same-pFr {var : Ty → Set}:
              {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : Ty}
              {μα μα' μβ μβ' μγ μγ' μδ μδ' : Tr} →
              pFr[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
              pFr[ var , τ₁' ⟨ μα' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μγ' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
              Set where
  App₁ : {τ β γ τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' : Ty} {μ₁ μ₂ μβ μβ' μγ μγ' : Tr} →
         (e₂ : Exp[ var ] τ ⟨ μ₁ ⟩ β ⟨ μ₂ ⟩ γ) →
         same-pFr {τ₃ = τ₃} {τ₃'} {τ₄} {τ₄'} {τ₅} {τ₅'} {μβ = μβ} {μβ'} {μγ} {μγ'}
                  (App₁ e₂) (App₁ e₂)
  App₂ : {τ₁ τ₂ α β τ₃ τ₃' : Ty} {μ₁ μ₂ μβ μβ' : Tr} →
         (v₁ : Val[ var ] (τ₁ ⇒ τ₂ ⟨ μ₁ ⟩ α ⟨ μ₂ ⟩ β) ) →
         same-pFr {τ₃ = τ₃} {τ₃'} {μβ = μβ} {μβ'}
                  (App₂ v₁) (App₂ v₁)

  Plus₁ : {α β γ τ₃ τ₃' : Ty} {μα μβ μγ μβ' : Tr} →
          (e₂ : Exp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
          same-pFr {τ₃ = τ₃} {τ₃'} {μβ = μβ} {μβ'}
                   (Plus₁ e₂) (Plus₁ e₂)

  Plus₂ : {τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
          (v₁ : Val[ var ] Nat) →
          same-pFr {τ₂ = τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                   (Plus₂ v₁) (Plus₂ v₁)

  Is0   : {τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
          same-pFr {τ₂ = τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                   Is0 Is0

  B2S   : {τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
          same-pFr {τ₂ = τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                   B2S B2S

-- Pure contexts
data pCxt[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : Ty → Set)
       : Ty → Tr → Ty → Tr → Ty → Ty → Tr → Ty → Tr → Ty → Set where
  Hole : {τ₁ τ₂ τ₃ : Ty} {μα μβ : Tr} →
          pCxt[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃
  Fr   : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : Ty}{μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : Tr} →
         (f : pFr[ var , τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉) →
         (c : pCxt[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆) →
         pCxt[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉

pCxt-plug : {var : Ty → Set}
            {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : Ty}{μα μβ μγ μδ : Tr} →
            pCxt[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
            Exp[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
            Exp[ var ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆

pCxt-plug Hole e₁ = e₁
pCxt-plug (Fr f p) e₁ = pFr-plug f (pCxt-plug p e₁)

data same-pCxt {var : Ty → Set} :
               {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : Ty}
               {μα μα' μβ μβ' μγ μγ' μδ μδ' : Tr} →
               pCxt[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
               pCxt[ var , τ₁' ⟨ μα' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μγ' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
               Set where
  Hole  : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
          same-pCxt {τ₁ = τ₁} {τ₁'} {τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                    Hole Hole
  Fr : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' τ₇ τ₇' τ₈' τ₈ τ₉ τ₉' : Ty}
       {μ₁ μ₁' μ₂ μ₂' μ₃ μ₃' μ₄ μ₄' μ₅ μ₅' μ₆ μ₆' : Tr} →
       {f₁ : pFr[ var , τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉} →
       {f₂ : pFr[ var , τ₄' ⟨ μ₃' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆' ] τ₇' ⟨ μ₅' ⟩ τ₈' ⟨ μ₆' ⟩ τ₉'} →
       same-pFr f₁ f₂ →
       {c₁ : pCxt[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆} →
       {c₂ : pCxt[ var , τ₁' ⟨ μ₁' ⟩ τ₂' ⟨ μ₂' ⟩ τ₃' ] τ₄' ⟨ μ₃' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆'} →
       same-pCxt c₁ c₂ →
       same-pCxt (Fr f₁ c₁) (Fr f₂ c₂)


-- One-step reduction (proof of Theorem 1)
data Reduce {var : Ty → Set} :
            {τ α β : Ty} {μα μβ : Tr} →
            Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β → Set where

  RBeta   : {τ₁ τ₂ α β : Ty} {μα μβ : Tr} →
            {e : var τ₁ → Exp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
            {v : Val[ var ] τ₁} →
            {e' : Exp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
            Subst e v e' →
            Reduce (App (Val (Abs e)) (Val v)) e'

  RPlus   : {α : Ty} {μα : Tr} {n₁ n₂ : ℕ} →
            Reduce {α = α} {μα = μα}
                   (Plus (Val (Num n₁)) (Val (Num n₂))) (Val (Num (n₁ + n₂)))

  RIs0    : {α : Ty} {μα : Tr} {n : ℕ} →
            Reduce {α = α} {μα = μα}
                   (Is0 (Val (Num n))) (Val (Bol (is0 n)))

  RB2S    : {α : Ty} {μα : Tr} {b : 𝔹} →
            Reduce {α = α} {μα = μα}
                   (B2S (Val (Bol b))) (Val (Str (b2s b)))

  RPrompt : {τ α : Ty} {μα : Tr} →
            {v : Val[ var ] τ} →
            Reduce {α = α} {μα = μα}
                   (Prompt refl (Val v)) (Val v)
            
  RControl : {τ α α' β β' γ γ' t₁ t₂ τ₁ τ₂ : Ty}
             {μ₀ μ₁ μᵢ μα μα' μβ μβ' μ₂ μ₃ : Tr} →
             (p₁ : pCxt[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
                       τ₁ ⟨ μ₃ ⟩ τ₂ ⟨ ● ⟩ β) →
             (p₂ : pCxt[ var , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ]
                       t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
             {x₀ : id-cont-type τ₁ μ₃ τ₂} →
             (x₁ : id-cont-type γ μᵢ γ') →
             (x₂ : compatible (t₁ ⇒⟨ μ₁ ⟩ t₂) μ₂ μ₀) →
             (x₃ : compatible μβ μ₀ μα) →
             same-pCxt p₁ p₂ →
             (e : var (τ ⇒ t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
                  Exp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) →
             Reduce {α = τ₂} {μα = μα}
                    (Prompt x₀ (pCxt-plug p₁ (Control x₁ x₂ x₃ e)))
                    (Prompt x₁ (App (Val (Abs e))
                      (Val (Abs (λ x → pCxt-plug p₂ (Val (Var x)))))))

  RFr     : {τ α β τ' α' β' : Ty} {μα μβ μα' μβ' : Tr}
            {e e' : Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
            (f : Fr[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
                      τ' ⟨ μα' ⟩ α' ⟨ μβ' ⟩ β') →
            Reduce e e' →
            Reduce (Fr-plug f e) (Fr-plug f e')
            
-- Multi-step reduction
data Reduce* {var : Ty → Set} :
               {τ α β : Ty} {μα μβ : Tr} →
               Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
               Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β → Set where

  R*Id    : {τ α β : Ty} {μα μβ : Tr} →
            (e : Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            Reduce* e e
            
  R*Trans : {τ α β : Ty} {μα μβ : Tr} →
            (e₁ : Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            (e₂ : Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            (e₃ : Exp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            Reduce e₁ e₂ →
            Reduce* e₂ e₃ →
            Reduce* e₁ e₃
