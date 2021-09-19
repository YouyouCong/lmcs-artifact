-- Reduction of fine-grained λF

module LambdaF-FG-Red where

open import LambdaF-FG
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

-- Substitution
data SubstVal {var : Ty → Set} : {τ₁ τ₂ : Ty} →
              (var τ₁ → Val[ var ] τ₂) →
              Val[ var ] τ₁ →
              Val[ var ] τ₂ → Set 

data SubstPExp {var : Ty → Set} : {τ₁ τ₂ : Ty} →
               (var τ₁ → PExp[ var ] τ₂) →
               Val[ var ] τ₁ →
               PExp[ var ] τ₂ → Set
              
data SubstIExp {var : Ty → Set} : {τ₁ τ₂ τ₃ τ₄ : Ty} {μα μβ : Tr} →
               (var τ₁ → IExp[ var ] τ₂ ⟨ μα ⟩ τ₃ ⟨ μβ ⟩ τ₄) →
               Val[ var ] τ₁ →
               IExp[ var ] τ₂ ⟨ μα ⟩ τ₃ ⟨ μβ ⟩ τ₄ → Set 

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

  sPAbs : {τ τ₁ τ₂ : Ty}
          {e : var τ₁ → var τ → PExp[ var ] τ₂}
          {v : Val[ var ] τ₁}
          {e' : var τ → PExp[ var ] τ₂} →
          ((x : var τ) → SubstPExp (λ y → (e y) x) v (e' x)) →
          SubstVal (λ y → PAbs (e y)) v (PAbs e')
          
  sIAbs : {τ τ₁ τ₂ α β γ : Ty} {μα μβ : Tr}
          {e : var τ₁ → var τ → IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β}
          {v : Val[ var ] τ₁}
          {e' : var τ → IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
          ((x : var τ) → SubstIExp (λ y → (e y) x) v (e' x)) →
          SubstVal (λ y → IAbs (e y)) v (IAbs e')

data SubstPExp {var} where
  sVal  : {τ τ₁ : Ty}
          {v₁ : var τ → Val[ var ] τ₁}
          {v : Val[ var ] τ}
          {v₁' : Val[ var ] τ₁} →
          SubstVal v₁ v v₁' →
          SubstPExp (λ y → Val (v₁ y)) v (Val v₁')

  sPPro : {τ β : Ty}
          {e : var τ → PExp[ var ] β}
          {v : Val[ var ] τ}
          {e' : PExp[ var ] β} →
          SubstPExp e v e' →
          SubstPExp (λ y → PPrompt (e y)) v (PPrompt e')

  sIPro : {τ β β' γ : Ty} {μᵢ μα : Tr}
          {e : var τ → IExp[ var ] β ⟨ μᵢ ⟩ β' ⟨ ● ⟩ γ}
          {v : Val[ var ] τ}
          {e' : IExp[ var ] β ⟨ μᵢ ⟩ β' ⟨ ● ⟩ γ}
          {x : id-cont-type β μᵢ β'} →
          SubstIExp e v e' →
          SubstPExp (λ y → IPrompt x (e y)) v (IPrompt x e')

  sPApp : {τ τ₁ τ₂ : Ty}
          {e₁ : var τ → PExp[ var ] (τ₁ ⇒p τ₂)}
          {e₂ : var τ → PExp[ var ] τ₁}
          {v : Val[ var ] τ}
          {e₁' : PExp[ var ] (τ₁ ⇒p τ₂)}
          {e₂' : PExp[ var ] τ₁} →
          SubstPExp e₁ v e₁' → SubstPExp e₂ v e₂' →
          SubstPExp (λ y → PApp (e₁ y) (e₂ y)) v (PApp e₁' e₂')

  sPPlu : {τ : Ty}
          {e₁ : var τ → PExp[ var ] Nat}
          {e₂ : var τ → PExp[ var ] Nat}
          {v : Val[ var ] τ}
          {e₁' : PExp[ var ] Nat}
          {e₂' : PExp[ var ] Nat} →
          SubstPExp e₁ v e₁' → SubstPExp e₂ v e₂' →
          SubstPExp (λ y → PPlus (e₁ y) (e₂ y)) v (PPlus e₁' e₂')

  sPIs0 : {τ : Ty}
          {e : var τ → PExp[ var ] Nat}
          {v : Val[ var ] τ}
          {e' : PExp[ var ] Nat} →
          SubstPExp e v e' → 
          SubstPExp (λ y → PIs0 (e y)) v (PIs0 e')

  sPB2S : {τ α β : Ty} {μα μβ : Tr}
          {e : var τ → PExp[ var ] Bool}
          {v : Val[ var ] τ}
          {e' : PExp[ var ] Bool} →
          SubstPExp e v e' → 
          SubstPExp (λ y → PB2S (e y)) v (PB2S e')

data SubstIExp {var} where
  sExp  : {τ τ₁ τ₃ : Ty} {μα : Tr}
          {e : var τ → PExp[ var ] τ₁}
          {v : Val[ var ] τ}
          {e' : PExp[ var ] τ₁} →
          SubstPExp e v e' →
          SubstIExp {τ₃ = τ₃} {μα = μα} (λ y → Exp (e y)) v (Exp e')

  sPIApp : {τ τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr}
           {e₁ : var τ → IExp[ var ] (τ₁ ⇒p τ₂) ⟨ μα ⟩ α ⟨ μβ ⟩ β}
           {e₂ : var τ → IExp[ var ] τ₁ ⟨ μγ ⟩ γ ⟨ μα ⟩ α}
           {v : Val[ var ] τ}
           {e₁' : IExp[ var ] (τ₁ ⇒p τ₂) ⟨ μα ⟩ α ⟨ μβ ⟩ β}
           {e₂' : IExp[ var ] τ₁ ⟨ μγ ⟩ γ ⟨ μα ⟩ α} →
           SubstIExp e₁ v e₁' → SubstIExp e₂ v e₂' →
           SubstIExp (λ y → PIApp (e₁ y) (e₂ y)) v (PIApp e₁' e₂')

  sIApp : {τ τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr}
          {e₁ : var τ → IExp[ var ] (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ}
          {e₂ : var τ → IExp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ}
          {v : Val[ var ] τ}
          {e₁' : IExp[ var ] (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ}
          {e₂' : IExp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ} →
          SubstIExp e₁ v e₁' → SubstIExp e₂ v e₂' →
          SubstIExp (λ y → IApp (e₁ y) (e₂ y)) v (IApp e₁' e₂')

  sIPlu : {τ α β γ : Ty} {μα μβ μγ : Tr}
          {e₁ : var τ → IExp[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ}
          {e₂ : var τ → IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β}
          {v : Val[ var ] τ}
          {e₁' : IExp[ var ] Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ}
          {e₂' : IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
          SubstIExp e₁ v e₁' → SubstIExp e₂ v e₂' →
          SubstIExp (λ y → IPlus (e₁ y) (e₂ y)) v (IPlus e₁' e₂')

  sIIs0 : {τ α β : Ty} {μα μβ : Tr}
          {e : var τ → IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β}
          {v : Val[ var ] τ}
          {e' : IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
          SubstIExp e v e' → 
          SubstIExp (λ y → IIs0 (e y)) v (IIs0 e')

  sIB2S : {τ α β : Ty} {μα μβ : Tr}
          {e : var τ → IExp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β}
          {v : Val[ var ] τ}
          {e' : IExp[ var ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
          SubstIExp e v e' → 
          SubstIExp (λ y → IB2S (e y)) v (IB2S e')

  sPCon : {τ τ₃ α β γ γ' : Ty} {μ₀ μ₁ μ₂ μᵢ μα : Tr} →
          {e : var τ₃ →
               var (τ ⇒p α) →
               IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β}
          {v : Val[ var ] τ₃}
          {e' : var (τ ⇒p α) →
                IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β}
          {x₁ : id-cont-type γ μᵢ γ'} →
          ((k : var (τ ⇒p α)) →
                SubstIExp (λ y → (e y) k) v ((e' k))) →
          SubstIExp {μα = μα}
                    (λ y → PControl x₁ (e y)) v (PControl x₁ e')
                   
  sICon : {τ τ₁ τ₁' τ₃ α β γ γ' : Ty} {μ₀ μ₁ μ₂ μᵢ μα μβ : Tr} →
          {e : var τ₃ →
               var (τ ⇒i τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α) →
               IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β}
          {v : Val[ var ] τ₃}
          {e' : var (τ ⇒i τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α) →
                IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β}
          {x₁ : id-cont-type γ μᵢ γ'}
          {x₂ : compatible (τ₁ ⇒⟨ μ₁ ⟩ τ₁') μ₂ μ₀}
          {x₃ : compatible  μβ μ₀ μα} →
          ((k : var (τ ⇒i τ₁ ⟨ μ₁ ⟩ τ₁' ⟨ μ₂ ⟩ α)) →
                SubstIExp (λ y → (e y) k) v ((e' k))) →
          SubstIExp (λ y → IControl x₁ x₂ x₃ (e y)) v (IControl x₁ x₂ x₃ e')
       

-- Frames
data PFr[_,_]_ (var : Ty → Set) : Ty → Ty → Set where
  PApp₁  : {τ₁ τ₂ : Ty} →
           (e₂ : PExp[ var ] τ₁) → PFr[ var , τ₁ ⇒p τ₂ ] τ₂

  PApp₂  : {τ₁ τ₂ : Ty} →
           (v₁ : Val[ var ] (τ₁ ⇒p τ₂)) → PFr[ var , τ₁ ] τ₂

  PPlus₁ : (e₂ : PExp[ var ] Nat) → PFr[ var , Nat ] Nat

  PPlus₂ : {α γ : Ty} {μα μγ : Tr} →
           (v₁ : Val[ var ] Nat) → PFr[ var , Nat ] Nat 

  PIs0   : {α β : Ty} {μα μβ : Tr} →
           PFr[ var , Nat ] Bool

  PB2S   : {α β : Ty} {μα μβ : Tr} →
           PFr[ var , Bool ] Str
           
data IFr[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : Ty → Set)
       : Ty → Tr → Ty → Tr → Ty → Ty → Tr → Ty → Tr → Ty → Set where
  PIApp₁ : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
           (e₂ : IExp[ var ] τ₁ ⟨ μγ ⟩ γ ⟨ μα ⟩ α) →
           IFr[ var , (τ₁ ⇒p τ₂) ⟨ μα ⟩ α ⟨ μβ ⟩ β ] τ₂ ⟨ μγ ⟩ γ ⟨ μβ ⟩ β

  PIApp₂ : {τ₁ τ₂ α β : Ty} {μα μβ : Tr} →
           (v₁ : Val[ var ] (τ₁ ⇒p τ₂)) →
           IFr[ var , τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β

  IApp₁  : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
           (e₂ : IExp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
           IFr[ var , (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ ]
              τ₂ ⟨ μα ⟩ α ⟨ μδ ⟩ δ

  IApp₂  : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
           (v₁ : Val[ var ] (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β)) →
           IFr[ var , τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ]
              τ₂ ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  IPlus₁ : {α β γ : Ty} {μα μβ μγ : Tr} →
           (e₂ : IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           IFr[ var , Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  IPlus₂ : {α γ : Ty} {μα μγ : Tr} →
           (v₁ : Val[ var ] Nat) →
           IFr[ var , Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  IIs0   : {α β : Ty} {μα μβ : Tr} →
           IFr[ var , Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β

  IB2S   : {α β : Ty} {μα μβ : Tr} →
           IFr[ var , Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Str ⟨ μα ⟩ α ⟨ μβ ⟩ β

PFr-plug : {var : Ty → Set} {τ₁ τ₂ : Ty} →
           PFr[ var , τ₁ ] τ₂ → PExp[ var ] τ₁ → PExp[ var ] τ₂
PFr-plug (PApp₁ e₂) e₁ = PApp e₁ e₂
PFr-plug (PApp₂ v₁) e₂ = PApp (Val v₁) e₂
PFr-plug (PPlus₁ e₂) e₁ = PPlus e₁ e₂
PFr-plug (PPlus₂ v₁) e₂ = PPlus (Val v₁) e₂
PFr-plug PIs0 e = PIs0 e
PFr-plug PB2S e = PB2S e
  
IFr-plug : {var : Ty → Set}
           {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : Ty} {μα μβ μγ μδ : Tr} →
           IFr[ var , τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆ →
           IExp[ var ] τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ →
           IExp[ var ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆
IFr-plug (PIApp₁ e₂) e₁ = PIApp e₁ e₂
IFr-plug (PIApp₂ v₁) e₂ = PIApp (Exp (Val v₁)) e₂          
IFr-plug (IApp₁ e₂) e₁ = IApp e₁ e₂
IFr-plug (IApp₂ v₁) e₂ = IApp (Exp (Val v₁)) e₂
IFr-plug (IPlus₁ e₂) e₁ = IPlus e₁ e₂
IFr-plug (IPlus₂ v₁) e₂ = IPlus (Exp (Val v₁)) e₂
IFr-plug IIs0 e = IIs0 e
IFr-plug IB2S e = IB2S e


-- Pure frames
data pPFr[_,_]_ (var : Ty → Set) : Ty → Ty → Set where
  PApp₁  : {τ₁ τ₂ : Ty} →
           (e₂ : PExp[ var ] τ₁) → pPFr[ var , τ₁ ⇒p τ₂ ] τ₂

  PApp₂  : {τ₁ τ₂ : Ty} →
           (v₁ : Val[ var ] (τ₁ ⇒p τ₂)) → pPFr[ var , τ₁ ] τ₂

  PPlus₁ : (e₂ : PExp[ var ] Nat) → pPFr[ var , Nat ] Nat

  PPlus₂ : (v₁ : Val[ var ] Nat) → pPFr[ var , Nat ] Nat 

  PIs0   : pPFr[ var , Nat ] Bool

  PB2S   : pPFr[ var , Bool ] Str
           
data pIFr[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : Ty → Set)
       : Ty → Tr → Ty → Tr → Ty → Ty → Tr → Ty → Tr → Ty → Set where
  PIApp₁ : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
           (e₂ : IExp[ var ] τ₁ ⟨ μγ ⟩ γ ⟨ μα ⟩ α) →
           pIFr[ var , (τ₁ ⇒p τ₂) ⟨ μα ⟩ α ⟨ μβ ⟩ β ] τ₂ ⟨ μγ ⟩ γ ⟨ μβ ⟩ β

  PIApp₂ : {τ₁ τ₂ α β : Ty} {μα μβ : Tr} →
           (v₁ : Val[ var ] (τ₁ ⇒p τ₂)) →
           pIFr[ var , τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β

  IApp₁  : {τ₁ τ₂ α β γ δ : Ty} {μα μβ μγ μδ : Tr} →
           (e₂ : IExp[ var ] τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ) →
           pIFr[ var , (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β) ⟨ μγ ⟩ γ ⟨ μδ ⟩ δ ]
             τ₂ ⟨ μα ⟩ α ⟨ μδ ⟩ δ

  IApp₂  : {τ₁ τ₂ α β γ : Ty} {μα μβ μγ : Tr} →
           (v₁ : Val[ var ] (τ₁ ⇒i τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β)) →
           pIFr[ var , τ₁ ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ]
             τ₂ ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  IPlus₁ : {α β γ : Ty} {μα μβ μγ : Tr} →
           (e₂ : IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           pIFr[ var , Nat ⟨ μβ ⟩ β ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  IPlus₂ : {α γ : Ty} {μα μγ : Tr} →
           (v₁ : Val[ var ] Nat) →
           pIFr[ var , Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ ] Nat ⟨ μα ⟩ α ⟨ μγ ⟩ γ

  IIs0   : {α β : Ty} {μα μβ : Tr} →
           pIFr[ var , Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β

  IB2S   : {α β : Ty} {μα μβ : Tr} →
           pIFr[ var , Bool ⟨ μα ⟩ α ⟨ μβ ⟩ β ] Str ⟨ μα ⟩ α ⟨ μβ ⟩ β

pPFr-plug : {var : Ty → Set} {τ₁ τ₂ : Ty} →
            pPFr[ var , τ₁ ] τ₂ → PExp[ var ] τ₁ → PExp[ var ] τ₂
pPFr-plug (PApp₁ e₂) e₁ = PApp e₁ e₂
pPFr-plug (PApp₂ v₁) e₂ = PApp (Val v₁) e₂
pPFr-plug (PPlus₁ e₂) e₁ = PPlus e₁ e₂
pPFr-plug (PPlus₂ v₁) e₂ = PPlus (Val v₁) e₂
pPFr-plug PIs0 e = PIs0 e
pPFr-plug PB2S e = PB2S e

pPFr-plugI : {var : Ty → Set} {τ₁ τ₂ α β : Ty} {μα μβ : Tr} →
             pPFr[ var , τ₁ ] τ₂ → IExp[ var ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
             IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β             
pPFr-plugI (PApp₁ e₂) e₁ = PIApp e₁ (Exp e₂)
pPFr-plugI (PApp₂ v₁) e₂ = PIApp (Exp (Val v₁)) e₂
pPFr-plugI (PPlus₁ e₂) e₁ = IPlus e₁ (Exp e₂)
pPFr-plugI (PPlus₂ v₁) e₂ = IPlus (Exp (Val v₁)) e₂
pPFr-plugI PIs0 e = IIs0 e
pPFr-plugI PB2S e = IB2S e

pIFr-plug : {var : Ty → Set}
            {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : Ty} {μα μβ μγ μδ : Tr} →
            pIFr[ var , τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆ →
            IExp[ var ] τ₂ ⟨ μα ⟩ τ₄ ⟨ μβ ⟩ τ₅ →
            IExp[ var ] τ₁ ⟨ μγ ⟩ τ₃ ⟨ μδ ⟩ τ₆          
pIFr-plug (PIApp₁ e₂) e₁ = PIApp e₁ e₂
pIFr-plug (PIApp₂ v₁) e₂ = PIApp (Exp (Val v₁)) e₂      
pIFr-plug (IApp₁ e₂) e₁ = IApp e₁ e₂
pIFr-plug (IApp₂ v₁) e₂ = IApp (Exp (Val v₁)) e₂
pIFr-plug (IPlus₁ e₂) e₁ = IPlus e₁ e₂
pIFr-plug (IPlus₂ v₁) e₂ = IPlus (Exp (Val v₁)) e₂
pIFr-plug IIs0 e = IIs0 e
pIFr-plug IB2S e = IB2S e            

data same-pIFr {var : Ty → Set} :
               {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : Ty}
               {μα μα' μβ μβ' μγ μγ' μδ μδ' : Tr} →
               pIFr[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
               pIFr[ var , τ₁' ⟨ μα' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μγ' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
               Set where           
  PIApp₁ : {τ β γ τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' : Ty} {μ₁ μ₂ μβ μβ' : Tr} →
           (e₂ : IExp[ var ] τ ⟨ μ₁ ⟩ β ⟨ μ₂ ⟩ γ) →
           same-pIFr {τ₃ = τ₃} {τ₃'} {τ₄} {τ₄'} {μβ = μβ} {μβ'} (PIApp₁ e₂) (PIApp₁ e₂)
                  
  PIApp₂ : {τ₁ τ₂ τ₂' α β τ₃ τ₃' : Ty} {μ₁ μ₂ μα μα' μβ μβ' : Tr} →
           (v₁ : Val[ var ] (τ₁ ⇒p τ₂)) →
           same-pIFr {τ₂ = τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                     (PIApp₂ v₁) (PIApp₂ v₁)

  IApp₁ : {τ β γ τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' : Ty} {μ₁ μ₂ μβ μβ' μγ μγ' : Tr} →
          (e₂ : IExp[ var ] τ ⟨ μ₁ ⟩ β ⟨ μ₂ ⟩ γ) →
          same-pIFr {τ₃ = τ₃} {τ₃'} {τ₄} {τ₄'} {τ₅} {τ₅'} {μβ = μβ} {μβ'} {μγ} {μγ'}
                    (IApp₁ e₂) (IApp₁ e₂)
                  
  IApp₂ : {τ₁ τ₂ α β τ₃ τ₃' : Ty} {μ₁ μ₂ μβ μβ' : Tr} →
          (v₁ : Val[ var ] (τ₁ ⇒i τ₂ ⟨ μ₁ ⟩ α ⟨ μ₂ ⟩ β)) →
          same-pIFr {τ₃ = τ₃} {τ₃'} {μβ = μβ} {μβ'}
                    (IApp₂ v₁) (IApp₂ v₁)

  IPlus₁ : {α β γ τ₃ τ₃' : Ty} {μα μβ μγ μβ' : Tr} →
           (e₂ : IExp[ var ] Nat ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
           same-pIFr {τ₃ = τ₃} {τ₃'} {μβ = μβ} {μβ'}
                     (IPlus₁ e₂) (IPlus₁ e₂)

  IPlus₂ : {τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
           (v₁ : Val[ var ] Nat) →
           same-pIFr {τ₂ = τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                     (IPlus₂ v₁) (IPlus₂ v₁)

  IIs0   : {τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
           same-pIFr {τ₂ = τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                     IIs0 IIs0

  IB2S   : {τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
           same-pIFr {τ₂ = τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                     IB2S IB2S


-- Pure contexts
data pPCxt[_,_]_ (var : Ty → Set) : Ty → Ty → Set where
  Hole : {τ₁ : Ty} → pPCxt[ var , τ₁ ] τ₁
  Fr   : {τ₁ τ₂ τ₃ : Ty} →
         (f : pPFr[ var , τ₂ ] τ₃) → (c : pPCxt[ var , τ₁ ] τ₂) →
         pPCxt[ var , τ₁ ] τ₃

pPCxt-plug : {var : Ty → Set} {τ₁ τ₂ : Ty} →
             pPCxt[ var , τ₁ ] τ₂ → PExp[ var ] τ₁ → PExp[ var ] τ₂
pPCxt-plug Hole e₁ = e₁
pPCxt-plug (Fr f p) e₁ = pPFr-plug f (pPCxt-plug p e₁)

pPCxt-plugI : {var : Ty → Set} {τ₁ τ₂ α β : Ty} {μα μβ : Tr} →
              pPCxt[ var , τ₁ ] τ₂ → IExp[ var ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
              IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β
pPCxt-plugI Hole e₁ = e₁
pPCxt-plugI (Fr f p) e₁ = pPFr-plugI f (pPCxt-plugI p e₁)

data pICxt[_,_⟨_⟩_⟨_⟩_]_⟨_⟩_⟨_⟩_ (var : Ty → Set)
       : Ty → Tr → Ty → Tr → Ty → Ty → Tr → Ty → Tr → Ty → Set where
  Hole : {τ₁ τ₂ τ₃ : Ty} {μα μβ : Tr} →
          pICxt[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃
  Fr   : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : Ty} {μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : Tr} →
         (f : pIFr[ var , τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉) →
         (c : pICxt[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆) →
         pICxt[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉

pICxt-plug : {var : Ty → Set}
            {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : Ty} {μα μβ μγ μδ : Tr} →
            pICxt[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
            IExp[ var ] τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ →
            IExp[ var ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆

pICxt-plug Hole e₁ = e₁
pICxt-plug (Fr f p) e₁ = pIFr-plug f (pICxt-plug p e₁)

data same-pICxt {var : Ty → Set} :
               {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : Ty}
               {μα μα' μβ μβ' μγ μγ' μδ μδ' : Tr} →
               pICxt[ var , τ₁ ⟨ μα ⟩ τ₂ ⟨ μβ ⟩ τ₃ ] τ₄ ⟨ μγ ⟩ τ₅ ⟨ μδ ⟩ τ₆ →
               pICxt[ var , τ₁' ⟨ μα' ⟩ τ₂' ⟨ μβ' ⟩ τ₃' ] τ₄' ⟨ μγ' ⟩ τ₅' ⟨ μδ' ⟩ τ₆' →
               Set where
  Hole  : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' : Ty} {μα μα' μβ μβ' : Tr} →
          same-pICxt {τ₁ = τ₁} {τ₁'} {τ₂} {τ₂'} {τ₃} {τ₃'} {μα = μα} {μα'} {μβ} {μβ'}
                     Hole Hole
  Fr : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' τ₇ τ₇' τ₈' τ₈ τ₉ τ₉' : Ty}
       {μ₁ μ₁' μ₂ μ₂' μ₃ μ₃' μ₄ μ₄' μ₅ μ₅' μ₆ μ₆' : Tr} →
       {f₁ : pIFr[ var , τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ ] τ₇ ⟨ μ₅ ⟩ τ₈ ⟨ μ₆ ⟩ τ₉ } →
       {f₂ : pIFr[ var , τ₄' ⟨ μ₃' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆' ] τ₇' ⟨ μ₅' ⟩ τ₈' ⟨ μ₆' ⟩ τ₉' } →
       same-pIFr f₁ f₂ →
       {c₁ : pICxt[ var , τ₁ ⟨ μ₁ ⟩ τ₂ ⟨ μ₂ ⟩ τ₃ ] τ₄ ⟨ μ₃ ⟩ τ₅ ⟨ μ₄ ⟩ τ₆ } →
       {c₂ : pICxt[ var , τ₁' ⟨ μ₁' ⟩ τ₂' ⟨ μ₂' ⟩ τ₃' ] τ₄' ⟨ μ₃' ⟩ τ₅' ⟨ μ₄' ⟩ τ₆' } →
       same-pICxt c₁ c₂ →
       same-pICxt (Fr f₁ c₁) (Fr f₂ c₂)


-- One-step reduction (proof of Theorem 6)
data PReduce {var : Ty → Set} :
             {τ₁ : Ty} →
             PExp[ var ] τ₁ → PExp[ var ] τ₁ → Set where
  RBeta     : {τ τ₁ : Ty}
              {e : var τ → PExp[ var ] τ₁}
              {v : Val[ var ] τ}
              {e' : PExp[ var ] τ₁} →
              SubstPExp e v e' →
              PReduce (PApp (Val (PAbs e)) (Val v)) e'
             
  RPlus     : {n₁ n₂ : ℕ} →
              PReduce (PPlus (Val (Num n₁)) (Val (Num n₂)))
                      (Val (Num (n₁ + n₂)))

  RIs0      : {n : ℕ} →
              PReduce (PIs0 (Val (Num n))) (Val (Bol (is0 n)))

  RB2S      : {b : 𝔹} →
              PReduce (PB2S (Val (Bol b))) (Val (Str (b2s b)))

  RPPrompt  : {τ : Ty} →
              {v₁ : Val[ var ] τ} →
              PReduce (PPrompt (Val v₁)) (Val v₁)

  RIPrompt  : {τ : Ty} →
              {v₁ : Val[ var ] τ} →
              PReduce (IPrompt refl (Exp (Val v₁))) (Val v₁)

  RPControl : {τ α β γ γ' : Ty}
              {μᵢ : Tr} →
              (p : pPCxt[ var , τ ] α) →
              (x₁ : id-cont-type γ μᵢ γ') →
              (e : var (τ ⇒p α) →
                   IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) →
              PReduce (IPrompt refl (pPCxt-plugI p (PControl x₁ e)))
                      (IPrompt x₁ (IApp (Exp (Val (IAbs e)))
                        (Exp (Val (PAbs (λ x → pPCxt-plug p (Val (Var x))))))))

  RIControl : {τ α α' β β' γ γ' t₁ t₂ τ₁ τ₂ : Ty}
              {μ₀ μ₁ μᵢ μα μα' μβ μβ' μ₂ μ₃ : Tr} →
              (p₁ : pICxt[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
                         τ₁ ⟨ μ₃ ⟩ τ₂ ⟨ ● ⟩ β) →
              (p₂ : pICxt[ var , τ ⟨ μα' ⟩ α' ⟨ μα' ⟩ α' ]
                         t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
              {x₀ : id-cont-type τ₁ μ₃ τ₂} →
              (x₁ : id-cont-type γ μᵢ γ') →
              (x₂ : compatible (t₁ ⇒⟨ μ₁ ⟩ t₂) μ₂ μ₀) →
              (x₃ : compatible μβ μ₀ μα) →
              same-pICxt p₁ p₂ →
              (e : var (τ ⇒i t₁ ⟨ μ₁ ⟩ t₂ ⟨ μ₂ ⟩ α) →
                   IExp[ var ] γ ⟨ μᵢ ⟩ γ' ⟨ ● ⟩ β) →
              PReduce (IPrompt x₀ (pICxt-plug p₁ (IControl x₁ x₂ x₃ e)))
                      (IPrompt x₁ (IApp (Exp (Val (IAbs e)))
                        (Exp (Val (IAbs (λ x → pICxt-plug p₂ (Exp (Val (Var x)))))))))
                        
  RFr      : {τ₁ τ₂ : Ty}
             {e e' : PExp[ var ] τ₁} →
             (f : PFr[ var , τ₁ ] τ₂) →
             PReduce e e' →
             PReduce (PFr-plug f e) (PFr-plug f e')
                     
data IReduce {var : Ty → Set} :
             {τ α β : Ty} {μα μβ : Tr} →
             IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
             IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β → Set where
  RExp   : {τ α : Ty} {μα : Tr} →
           {e e' : PExp[ var ] τ} →
           PReduce e e' → IReduce {α = α} {μα = μα} (Exp e) (Exp e')

  RBeta  : {τ₁ τ₂ α β : Ty} {μα μβ : Tr}
           {e : var τ₁ → IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β}
           {v : Val[ var ] τ₁}
           {e' : IExp[ var ] τ₂ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
           SubstIExp e v e' →
           IReduce (IApp (Exp (Val (IAbs e))) (Exp (Val v))) e'

  RPBeta : {τ₁ τ₂ α β : Ty} {μα : Tr}
           {e : var τ₁ → PExp[ var ] τ₂}
           {v : Val[ var ] τ₁}
           {e' : PExp[ var ] τ₂} →
           SubstPExp e v e' →
           IReduce {α = α} {μα = μα}
                   (PIApp (Exp (Val (PAbs e))) (Exp (Val v))) (Exp e')

  RPlus  : {α : Ty} {μα : Tr} {n₁ n₂ : ℕ} →
           IReduce {α = α} {μα = μα}
                   (IPlus (Exp (Val (Num n₁))) (Exp (Val (Num n₂))))
                   (Exp (Val (Num (n₁ + n₂))))

  RIs0   : {α : Ty} {μα : Tr} {n : ℕ} →
           IReduce {α = α} {μα = μα}
                   (IIs0 (Exp (Val (Num n)))) (Exp (Val (Bol (is0 n))))

  RB2S   : {α : Ty} {μα : Tr} {b : 𝔹} →
           IReduce {α = α} {μα = μα}
                   (IB2S (Exp (Val (Bol b)))) (Exp (Val (Str (b2s b))))         

  RFr    : {τ α β τ' α' β' : Ty} {μα μβ μα' μβ' : Tr}
           {e e' : IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β} →
           (f : IFr[ var , τ ⟨ μα ⟩ α ⟨ μβ ⟩ β ]
                   τ' ⟨ μα' ⟩ α' ⟨ μβ' ⟩ β') →
           IReduce e e' →
           IReduce (IFr-plug f e) (IFr-plug f e')


-- Multi-step reduction
data IReduce* {var : Ty → Set} :
              {τ α β : Ty} {μα μβ : Tr} →
              IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
              IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β → Set where

  R*Id    : {τ α β : Ty} {μα μβ : Tr} →
            (e : IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            IReduce* e e
            
  R*Trans : {τ α β : Ty} {μα μβ : Tr} →
            (e₁ : IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            (e₂ : IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            (e₃ : IExp[ var ] τ ⟨ μα ⟩ α ⟨ μβ ⟩ β) →
            IReduce e₁ e₂ →
            IReduce* e₂ e₃ →
            IReduce* e₁ e₃
