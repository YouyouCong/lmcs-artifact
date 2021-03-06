-- Reduction of fine-grained Ξ»F

module LambdaF-FG-Red where

open import LambdaF-FG
open import Data.Nat using (β; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to πΉ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality

-- Substitution
data SubstVal {var : Ty β Set} : {Οβ Οβ : Ty} β
              (var Οβ β Val[ var ] Οβ) β
              Val[ var ] Οβ β
              Val[ var ] Οβ β Set 

data SubstPExp {var : Ty β Set} : {Οβ Οβ : Ty} β
               (var Οβ β PExp[ var ] Οβ) β
               Val[ var ] Οβ β
               PExp[ var ] Οβ β Set
              
data SubstIExp {var : Ty β Set} : {Οβ Οβ Οβ Οβ : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
               (var Οβ β IExp[ var ] Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ) β
               Val[ var ] Οβ β
               IExp[ var ] Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ β Set 

data SubstVal {var} where
  sVar= : {Ο : Ty} {v : Val[ var ] Ο} β
          SubstVal (Ξ» x β Var x) v v

  sVarβ  : {Οβ Οβ : Ty} {v : Val[ var ] Οβ} {x : var Οβ} β
          SubstVal (Ξ» y β Var x) v (Var x)

  sNum  : {Ο : Ty} {n : β}
          {v : Val[ var ] Ο} β
          SubstVal (Ξ» x β Num n) v (Num n)

  sBol  : {Ο : Ty} {b : πΉ}
          {v : Val[ var ] Ο} β
          SubstVal (Ξ» x β Bol b) v (Bol b)

  sStr  : {Ο : Ty} {s : String}
          {v : Val[ var ] Ο} β
          SubstVal (Ξ» x β Str s) v (Str s)

  sPAbs : {Ο Οβ Οβ : Ty}
          {e : var Οβ β var Ο β PExp[ var ] Οβ}
          {v : Val[ var ] Οβ}
          {e' : var Ο β PExp[ var ] Οβ} β
          ((x : var Ο) β SubstPExp (Ξ» y β (e y) x) v (e' x)) β
          SubstVal (Ξ» y β PAbs (e y)) v (PAbs e')
          
  sIAbs : {Ο Οβ Οβ Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² : Tr}
          {e : var Οβ β var Ο β IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²}
          {v : Val[ var ] Οβ}
          {e' : var Ο β IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²} β
          ((x : var Ο) β SubstIExp (Ξ» y β (e y) x) v (e' x)) β
          SubstVal (Ξ» y β IAbs (e y)) v (IAbs e')

data SubstPExp {var} where
  sVal  : {Ο Οβ : Ty}
          {vβ : var Ο β Val[ var ] Οβ}
          {v : Val[ var ] Ο}
          {vβ' : Val[ var ] Οβ} β
          SubstVal vβ v vβ' β
          SubstPExp (Ξ» y β Val (vβ y)) v (Val vβ')

  sPro  : {Ο Ξ² Ξ²' Ξ³ : Ty} {ΞΌα΅’ ΞΌΞ± : Tr}
          {e : var Ο β IExp[ var ] Ξ² β¨ ΞΌα΅’ β© Ξ²' β¨ β β© Ξ³}
          {v : Val[ var ] Ο}
          {e' : IExp[ var ] Ξ² β¨ ΞΌα΅’ β© Ξ²' β¨ β β© Ξ³}
          {x : id-cont-type Ξ² ΞΌα΅’ Ξ²'} β
          SubstIExp e v e' β
          SubstPExp (Ξ» y β Prompt x (e y)) v (Prompt x e')

  sPApp : {Ο Οβ Οβ : Ty}
          {eβ : var Ο β PExp[ var ] (Οβ βp Οβ)}
          {eβ : var Ο β PExp[ var ] Οβ}
          {v : Val[ var ] Ο}
          {eβ' : PExp[ var ] (Οβ βp Οβ)}
          {eβ' : PExp[ var ] Οβ} β
          SubstPExp eβ v eβ' β SubstPExp eβ v eβ' β
          SubstPExp (Ξ» y β PApp (eβ y) (eβ y)) v (PApp eβ' eβ')

  sPPlu : {Ο : Ty}
          {eβ : var Ο β PExp[ var ] Nat}
          {eβ : var Ο β PExp[ var ] Nat}
          {v : Val[ var ] Ο}
          {eβ' : PExp[ var ] Nat}
          {eβ' : PExp[ var ] Nat} β
          SubstPExp eβ v eβ' β SubstPExp eβ v eβ' β
          SubstPExp (Ξ» y β PPlus (eβ y) (eβ y)) v (PPlus eβ' eβ')

  sPIs0 : {Ο : Ty}
          {e : var Ο β PExp[ var ] Nat}
          {v : Val[ var ] Ο}
          {e' : PExp[ var ] Nat} β
          SubstPExp e v e' β 
          SubstPExp (Ξ» y β PIs0 (e y)) v (PIs0 e')

  sPB2S : {Ο Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr}
          {e : var Ο β PExp[ var ] Bool}
          {v : Val[ var ] Ο}
          {e' : PExp[ var ] Bool} β
          SubstPExp e v e' β 
          SubstPExp (Ξ» y β PB2S (e y)) v (PB2S e')

data SubstIExp {var} where
  sExp  : {Ο Οβ Οβ : Ty} {ΞΌΞ± : Tr}
          {e : var Ο β PExp[ var ] Οβ}
          {v : Val[ var ] Ο}
          {e' : PExp[ var ] Οβ} β
          SubstPExp e v e' β
          SubstIExp {Οβ = Οβ} {ΞΌΞ± = ΞΌΞ±} (Ξ» y β Exp (e y)) v (Exp e')

  sPIApp : {Ο Οβ Οβ Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr}
           {eβ : var Ο β IExp[ var ] (Οβ βp Οβ) β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²}
           {eβ : var Ο β IExp[ var ] Οβ β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ± β© Ξ±}
           {v : Val[ var ] Ο}
           {eβ' : IExp[ var ] (Οβ βp Οβ) β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²}
           {eβ' : IExp[ var ] Οβ β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ± β© Ξ±} β
           SubstIExp eβ v eβ' β SubstIExp eβ v eβ' β
           SubstIExp (Ξ» y β PIApp (eβ y) (eβ y)) v (PIApp eβ' eβ')

  sIApp : {Ο Οβ Οβ Ξ± Ξ² Ξ³ Ξ΄ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ ΞΌΞ΄ : Tr}
          {eβ : var Ο β IExp[ var ] (Οβ βi Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ΄ β© Ξ΄}
          {eβ : var Ο β IExp[ var ] Οβ β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³}
          {v : Val[ var ] Ο}
          {eβ' : IExp[ var ] (Οβ βi Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ΄ β© Ξ΄}
          {eβ' : IExp[ var ] Οβ β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³} β
          SubstIExp eβ v eβ' β SubstIExp eβ v eβ' β
          SubstIExp (Ξ» y β IApp (eβ y) (eβ y)) v (IApp eβ' eβ')

  sIPlu : {Ο Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr}
          {eβ : var Ο β IExp[ var ] Nat β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³}
          {eβ : var Ο β IExp[ var ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²}
          {v : Val[ var ] Ο}
          {eβ' : IExp[ var ] Nat β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³}
          {eβ' : IExp[ var ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²} β
          SubstIExp eβ v eβ' β SubstIExp eβ v eβ' β
          SubstIExp (Ξ» y β IPlus (eβ y) (eβ y)) v (IPlus eβ' eβ')

  sIIs0 : {Ο Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr}
          {e : var Ο β IExp[ var ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²}
          {v : Val[ var ] Ο}
          {e' : IExp[ var ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²} β
          SubstIExp e v e' β 
          SubstIExp (Ξ» y β IIs0 (e y)) v (IIs0 e')

  sIB2S : {Ο Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr}
          {e : var Ο β IExp[ var ] Bool β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²}
          {v : Val[ var ] Ο}
          {e' : IExp[ var ] Bool β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²} β
          SubstIExp e v e' β 
          SubstIExp (Ξ» y β IB2S (e y)) v (IB2S e')

  sPCon : {Ο Οβ Ξ± Ξ² Ξ³ Ξ³' : Ty} {ΞΌβ ΞΌβ ΞΌβ ΞΌα΅’ ΞΌΞ± : Tr} β
          {e : var Οβ β
               var (Ο βp Ξ±) β
               IExp[ var ] Ξ³ β¨ ΞΌα΅’ β© Ξ³' β¨ β β© Ξ²}
          {v : Val[ var ] Οβ}
          {e' : var (Ο βp Ξ±) β
                IExp[ var ] Ξ³ β¨ ΞΌα΅’ β© Ξ³' β¨ β β© Ξ²}
          {xβ : id-cont-type Ξ³ ΞΌα΅’ Ξ³'} β
          ((k : var (Ο βp Ξ±)) β
                SubstIExp (Ξ» y β (e y) k) v ((e' k))) β
          SubstIExp {ΞΌΞ± = ΞΌΞ±}
                    (Ξ» y β PControl xβ (e y)) v (PControl xβ e')
                   
  sICon : {Ο Οβ Οβ' Οβ Ξ± Ξ² Ξ³ Ξ³' : Ty} {ΞΌβ ΞΌβ ΞΌβ ΞΌα΅’ ΞΌΞ± ΞΌΞ² : Tr} β
          {e : var Οβ β
               var (Ο βi Οβ β¨ ΞΌβ β© Οβ' β¨ ΞΌβ β© Ξ±) β
               IExp[ var ] Ξ³ β¨ ΞΌα΅’ β© Ξ³' β¨ β β© Ξ²}
          {v : Val[ var ] Οβ}
          {e' : var (Ο βi Οβ β¨ ΞΌβ β© Οβ' β¨ ΞΌβ β© Ξ±) β
                IExp[ var ] Ξ³ β¨ ΞΌα΅’ β© Ξ³' β¨ β β© Ξ²}
          {xβ : id-cont-type Ξ³ ΞΌα΅’ Ξ³'}
          {xβ : compatible (Οβ ββ¨ ΞΌβ β© Οβ') ΞΌβ ΞΌβ}
          {xβ : compatible  ΞΌΞ² ΞΌβ ΞΌΞ±} β
          ((k : var (Ο βi Οβ β¨ ΞΌβ β© Οβ' β¨ ΞΌβ β© Ξ±)) β
                SubstIExp (Ξ» y β (e y) k) v ((e' k))) β
          SubstIExp (Ξ» y β IControl xβ xβ xβ (e y)) v (IControl xβ xβ xβ e')
       

-- Frames
data PFr[_,_]_ (var : Ty β Set) : Ty β Ty β Set where
  PAppβ  : {Οβ Οβ : Ty} β
           (eβ : PExp[ var ] Οβ) β PFr[ var , Οβ βp Οβ ] Οβ

  PAppβ  : {Οβ Οβ : Ty} β
           (vβ : Val[ var ] (Οβ βp Οβ)) β PFr[ var , Οβ ] Οβ

  PPlusβ : (eβ : PExp[ var ] Nat) β PFr[ var , Nat ] Nat

  PPlusβ : {Ξ± Ξ³ : Ty} {ΞΌΞ± ΞΌΞ³ : Tr} β
           (vβ : Val[ var ] Nat) β PFr[ var , Nat ] Nat 

  PIs0   : {Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           PFr[ var , Nat ] Bool

  PB2S   : {Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           PFr[ var , Bool ] Str
           
data IFr[_,_β¨_β©_β¨_β©_]_β¨_β©_β¨_β©_ (var : Ty β Set)
       : Ty β Tr β Ty β Tr β Ty β Ty β Tr β Ty β Tr β Ty β Set where
  PIAppβ : {Οβ Οβ Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr} β
           (eβ : IExp[ var ] Οβ β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ± β© Ξ±) β
           IFr[ var , (Οβ βp Οβ) β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Οβ β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ² β© Ξ²

  PIAppβ : {Οβ Οβ Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           (vβ : Val[ var ] (Οβ βp Οβ)) β
           IFr[ var , Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²

  IAppβ  : {Οβ Οβ Ξ± Ξ² Ξ³ Ξ΄ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ ΞΌΞ΄ : Tr} β
           (eβ : IExp[ var ] Οβ β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³) β
           IFr[ var , (Οβ βi Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ΄ β© Ξ΄ ]
              Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ΄ β© Ξ΄

  IAppβ  : {Οβ Οβ Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr} β
           (vβ : Val[ var ] (Οβ βi Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²)) β
           IFr[ var , Οβ β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³ ]
              Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³

  IPlusβ : {Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr} β
           (eβ : IExp[ var ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β
           IFr[ var , Nat β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³ ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³

  IPlusβ : {Ξ± Ξ³ : Ty} {ΞΌΞ± ΞΌΞ³ : Tr} β
           (vβ : Val[ var ] Nat) β
           IFr[ var , Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³ ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³

  IIs0   : {Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           IFr[ var , Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Bool β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²

  IB2S   : {Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           IFr[ var , Bool β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Str β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²

PFr-plug : {var : Ty β Set} {Οβ Οβ : Ty} β
           PFr[ var , Οβ ] Οβ β PExp[ var ] Οβ β PExp[ var ] Οβ
PFr-plug (PAppβ eβ) eβ = PApp eβ eβ
PFr-plug (PAppβ vβ) eβ = PApp (Val vβ) eβ
PFr-plug (PPlusβ eβ) eβ = PPlus eβ eβ
PFr-plug (PPlusβ vβ) eβ = PPlus (Val vβ) eβ
PFr-plug PIs0 e = PIs0 e
PFr-plug PB2S e = PB2S e
  
IFr-plug : {var : Ty β Set}
           {Οβ Οβ Οβ Οβ Οβ Οβ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ ΞΌΞ΄ : Tr} β
           IFr[ var , Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ β
           IExp[ var ] Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ β
           IExp[ var ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ
IFr-plug (PIAppβ eβ) eβ = PIApp eβ eβ
IFr-plug (PIAppβ vβ) eβ = PIApp (Exp (Val vβ)) eβ          
IFr-plug (IAppβ eβ) eβ = IApp eβ eβ
IFr-plug (IAppβ vβ) eβ = IApp (Exp (Val vβ)) eβ
IFr-plug (IPlusβ eβ) eβ = IPlus eβ eβ
IFr-plug (IPlusβ vβ) eβ = IPlus (Exp (Val vβ)) eβ
IFr-plug IIs0 e = IIs0 e
IFr-plug IB2S e = IB2S e


-- Pure frames
data pPFr[_,_]_ (var : Ty β Set) : Ty β Ty β Set where
  PAppβ  : {Οβ Οβ : Ty} β
           (eβ : PExp[ var ] Οβ) β pPFr[ var , Οβ βp Οβ ] Οβ

  PAppβ  : {Οβ Οβ : Ty} β
           (vβ : Val[ var ] (Οβ βp Οβ)) β pPFr[ var , Οβ ] Οβ

  PPlusβ : (eβ : PExp[ var ] Nat) β pPFr[ var , Nat ] Nat

  PPlusβ : (vβ : Val[ var ] Nat) β pPFr[ var , Nat ] Nat 

  PIs0   : pPFr[ var , Nat ] Bool

  PB2S   : pPFr[ var , Bool ] Str
           
data pIFr[_,_β¨_β©_β¨_β©_]_β¨_β©_β¨_β©_ (var : Ty β Set)
       : Ty β Tr β Ty β Tr β Ty β Ty β Tr β Ty β Tr β Ty β Set where
  PIAppβ : {Οβ Οβ Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr} β
           (eβ : IExp[ var ] Οβ β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ± β© Ξ±) β
           pIFr[ var , (Οβ βp Οβ) β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Οβ β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ² β© Ξ²

  PIAppβ : {Οβ Οβ Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           (vβ : Val[ var ] (Οβ βp Οβ)) β
           pIFr[ var , Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²

  IAppβ  : {Οβ Οβ Ξ± Ξ² Ξ³ Ξ΄ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ ΞΌΞ΄ : Tr} β
           (eβ : IExp[ var ] Οβ β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³) β
           pIFr[ var , (Οβ βi Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β¨ ΞΌΞ³ β© Ξ³ β¨ ΞΌΞ΄ β© Ξ΄ ]
             Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ΄ β© Ξ΄

  IAppβ  : {Οβ Οβ Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr} β
           (vβ : Val[ var ] (Οβ βi Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²)) β
           pIFr[ var , Οβ β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³ ]
             Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³

  IPlusβ : {Ξ± Ξ² Ξ³ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ : Tr} β
           (eβ : IExp[ var ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β
           pIFr[ var , Nat β¨ ΞΌΞ² β© Ξ² β¨ ΞΌΞ³ β© Ξ³ ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³

  IPlusβ : {Ξ± Ξ³ : Ty} {ΞΌΞ± ΞΌΞ³ : Tr} β
           (vβ : Val[ var ] Nat) β
           pIFr[ var , Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³ ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ³ β© Ξ³

  IIs0   : {Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           pIFr[ var , Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Bool β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²

  IB2S   : {Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
           pIFr[ var , Bool β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ] Str β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²

pPFr-plug : {var : Ty β Set} {Οβ Οβ : Ty} β
            pPFr[ var , Οβ ] Οβ β PExp[ var ] Οβ β PExp[ var ] Οβ
pPFr-plug (PAppβ eβ) eβ = PApp eβ eβ
pPFr-plug (PAppβ vβ) eβ = PApp (Val vβ) eβ
pPFr-plug (PPlusβ eβ) eβ = PPlus eβ eβ
pPFr-plug (PPlusβ vβ) eβ = PPlus (Val vβ) eβ
pPFr-plug PIs0 e = PIs0 e
pPFr-plug PB2S e = PB2S e

pPFr-plugI : {var : Ty β Set} {Οβ Οβ Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
             pPFr[ var , Οβ ] Οβ β IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² β
             IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²             
pPFr-plugI (PAppβ eβ) eβ = PIApp eβ (Exp eβ)
pPFr-plugI (PAppβ vβ) eβ = PIApp (Exp (Val vβ)) eβ
pPFr-plugI (PPlusβ eβ) eβ = IPlus eβ (Exp eβ)
pPFr-plugI (PPlusβ vβ) eβ = IPlus (Exp (Val vβ)) eβ
pPFr-plugI PIs0 e = IIs0 e
pPFr-plugI PB2S e = IB2S e

pIFr-plug : {var : Ty β Set}
            {Οβ Οβ Οβ Οβ Οβ Οβ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ ΞΌΞ΄ : Tr} β
            pIFr[ var , Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ β
            IExp[ var ] Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ β
            IExp[ var ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ          
pIFr-plug (PIAppβ eβ) eβ = PIApp eβ eβ
pIFr-plug (PIAppβ vβ) eβ = PIApp (Exp (Val vβ)) eβ      
pIFr-plug (IAppβ eβ) eβ = IApp eβ eβ
pIFr-plug (IAppβ vβ) eβ = IApp (Exp (Val vβ)) eβ
pIFr-plug (IPlusβ eβ) eβ = IPlus eβ eβ
pIFr-plug (IPlusβ vβ) eβ = IPlus (Exp (Val vβ)) eβ
pIFr-plug IIs0 e = IIs0 e
pIFr-plug IB2S e = IB2S e            

data same-pIFr {var : Ty β Set} :
               {Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' : Ty}
               {ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' ΞΌΞ³ ΞΌΞ³' ΞΌΞ΄ ΞΌΞ΄' : Tr} β
               pIFr[ var , Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ β
               pIFr[ var , Οβ' β¨ ΞΌΞ±' β© Οβ' β¨ ΞΌΞ²' β© Οβ' ] Οβ' β¨ ΞΌΞ³' β© Οβ' β¨ ΞΌΞ΄' β© Οβ' β
               Set where           
  PIAppβ : {Ο Ξ² Ξ³ Οβ Οβ' Οβ Οβ' Οβ Οβ' : Ty} {ΞΌβ ΞΌβ ΞΌΞ² ΞΌΞ²' : Tr} β
           (eβ : IExp[ var ] Ο β¨ ΞΌβ β© Ξ² β¨ ΞΌβ β© Ξ³) β
           same-pIFr {Οβ = Οβ} {Οβ'} {Οβ} {Οβ'} {ΞΌΞ² = ΞΌΞ²} {ΞΌΞ²'} (PIAppβ eβ) (PIAppβ eβ)
                  
  PIAppβ : {Οβ Οβ Οβ' Ξ± Ξ² Οβ Οβ' : Ty} {ΞΌβ ΞΌβ ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' : Tr} β
           (vβ : Val[ var ] (Οβ βp Οβ)) β
           same-pIFr {Οβ = Οβ} {Οβ'} {Οβ} {Οβ'} {ΞΌΞ± = ΞΌΞ±} {ΞΌΞ±'} {ΞΌΞ²} {ΞΌΞ²'}
                     (PIAppβ vβ) (PIAppβ vβ)

  IAppβ : {Ο Ξ² Ξ³ Οβ Οβ' Οβ Οβ' Οβ Οβ' : Ty} {ΞΌβ ΞΌβ ΞΌΞ² ΞΌΞ²' ΞΌΞ³ ΞΌΞ³' : Tr} β
          (eβ : IExp[ var ] Ο β¨ ΞΌβ β© Ξ² β¨ ΞΌβ β© Ξ³) β
          same-pIFr {Οβ = Οβ} {Οβ'} {Οβ} {Οβ'} {Οβ} {Οβ'} {ΞΌΞ² = ΞΌΞ²} {ΞΌΞ²'} {ΞΌΞ³} {ΞΌΞ³'}
                    (IAppβ eβ) (IAppβ eβ)
                  
  IAppβ : {Οβ Οβ Ξ± Ξ² Οβ Οβ' : Ty} {ΞΌβ ΞΌβ ΞΌΞ² ΞΌΞ²' : Tr} β
          (vβ : Val[ var ] (Οβ βi Οβ β¨ ΞΌβ β© Ξ± β¨ ΞΌβ β© Ξ²)) β
          same-pIFr {Οβ = Οβ} {Οβ'} {ΞΌΞ² = ΞΌΞ²} {ΞΌΞ²'}
                    (IAppβ vβ) (IAppβ vβ)

  IPlusβ : {Ξ± Ξ² Ξ³ Οβ Οβ' : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ ΞΌΞ²' : Tr} β
           (eβ : IExp[ var ] Nat β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β
           same-pIFr {Οβ = Οβ} {Οβ'} {ΞΌΞ² = ΞΌΞ²} {ΞΌΞ²'}
                     (IPlusβ eβ) (IPlusβ eβ)

  IPlusβ : {Οβ Οβ' Οβ Οβ' : Ty} {ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' : Tr} β
           (vβ : Val[ var ] Nat) β
           same-pIFr {Οβ = Οβ} {Οβ'} {Οβ} {Οβ'} {ΞΌΞ± = ΞΌΞ±} {ΞΌΞ±'} {ΞΌΞ²} {ΞΌΞ²'}
                     (IPlusβ vβ) (IPlusβ vβ)

  IIs0   : {Οβ Οβ' Οβ Οβ' : Ty} {ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' : Tr} β
           same-pIFr {Οβ = Οβ} {Οβ'} {Οβ} {Οβ'} {ΞΌΞ± = ΞΌΞ±} {ΞΌΞ±'} {ΞΌΞ²} {ΞΌΞ²'}
                     IIs0 IIs0

  IB2S   : {Οβ Οβ' Οβ Οβ' : Ty} {ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' : Tr} β
           same-pIFr {Οβ = Οβ} {Οβ'} {Οβ} {Οβ'} {ΞΌΞ± = ΞΌΞ±} {ΞΌΞ±'} {ΞΌΞ²} {ΞΌΞ²'}
                     IB2S IB2S


-- Pure contexts
data pPCxt[_,_]_ (var : Ty β Set) : Ty β Ty β Set where
  Hole : {Οβ : Ty} β pPCxt[ var , Οβ ] Οβ
  Fr   : {Οβ Οβ Οβ : Ty} β
         (f : pPFr[ var , Οβ ] Οβ) β (c : pPCxt[ var , Οβ ] Οβ) β
         pPCxt[ var , Οβ ] Οβ

pPCxt-plug : {var : Ty β Set} {Οβ Οβ : Ty} β
             pPCxt[ var , Οβ ] Οβ β PExp[ var ] Οβ β PExp[ var ] Οβ
pPCxt-plug Hole eβ = eβ
pPCxt-plug (Fr f p) eβ = pPFr-plug f (pPCxt-plug p eβ)

pPCxt-plugI : {var : Ty β Set} {Οβ Οβ Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
              pPCxt[ var , Οβ ] Οβ β IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² β
              IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²
pPCxt-plugI Hole eβ = eβ
pPCxt-plugI (Fr f p) eβ = pPFr-plugI f (pPCxt-plugI p eβ)

data pICxt[_,_β¨_β©_β¨_β©_]_β¨_β©_β¨_β©_ (var : Ty β Set)
       : Ty β Tr β Ty β Tr β Ty β Ty β Tr β Ty β Tr β Ty β Set where
  Hole : {Οβ Οβ Οβ : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
          pICxt[ var , Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ ] Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ
  Fr   : {Οβ Οβ Οβ Οβ Οβ Οβ Οβ Οβ Οβ : Ty} {ΞΌβ ΞΌβ ΞΌβ ΞΌβ ΞΌβ ΞΌβ : Tr} β
         (f : pIFr[ var , Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ ] Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ) β
         (c : pICxt[ var , Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ ] Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ) β
         pICxt[ var , Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ ] Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ

pICxt-plug : {var : Ty β Set}
            {Οβ Οβ Οβ Οβ Οβ Οβ : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ³ ΞΌΞ΄ : Tr} β
            pICxt[ var , Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ β
            IExp[ var ] Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ β
            IExp[ var ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ

pICxt-plug Hole eβ = eβ
pICxt-plug (Fr f p) eβ = pIFr-plug f (pICxt-plug p eβ)

data same-pICxt {var : Ty β Set} :
               {Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' : Ty}
               {ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' ΞΌΞ³ ΞΌΞ³' ΞΌΞ΄ ΞΌΞ΄' : Tr} β
               pICxt[ var , Οβ β¨ ΞΌΞ± β© Οβ β¨ ΞΌΞ² β© Οβ ] Οβ β¨ ΞΌΞ³ β© Οβ β¨ ΞΌΞ΄ β© Οβ β
               pICxt[ var , Οβ' β¨ ΞΌΞ±' β© Οβ' β¨ ΞΌΞ²' β© Οβ' ] Οβ' β¨ ΞΌΞ³' β© Οβ' β¨ ΞΌΞ΄' β© Οβ' β
               Set where
  Hole  : {Οβ Οβ' Οβ Οβ' Οβ Οβ' : Ty} {ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' : Tr} β
          same-pICxt {Οβ = Οβ} {Οβ'} {Οβ} {Οβ'} {Οβ} {Οβ'} {ΞΌΞ± = ΞΌΞ±} {ΞΌΞ±'} {ΞΌΞ²} {ΞΌΞ²'}
                     Hole Hole
  Fr : {Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ Οβ' Οβ' Οβ Οβ Οβ' : Ty}
       {ΞΌβ ΞΌβ' ΞΌβ ΞΌβ' ΞΌβ ΞΌβ' ΞΌβ ΞΌβ' ΞΌβ ΞΌβ' ΞΌβ ΞΌβ' : Tr} β
       {fβ : pIFr[ var , Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ ] Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ } β
       {fβ : pIFr[ var , Οβ' β¨ ΞΌβ' β© Οβ' β¨ ΞΌβ' β© Οβ' ] Οβ' β¨ ΞΌβ' β© Οβ' β¨ ΞΌβ' β© Οβ' } β
       same-pIFr fβ fβ β
       {cβ : pICxt[ var , Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ ] Οβ β¨ ΞΌβ β© Οβ β¨ ΞΌβ β© Οβ } β
       {cβ : pICxt[ var , Οβ' β¨ ΞΌβ' β© Οβ' β¨ ΞΌβ' β© Οβ' ] Οβ' β¨ ΞΌβ' β© Οβ' β¨ ΞΌβ' β© Οβ' } β
       same-pICxt cβ cβ β
       same-pICxt (Fr fβ cβ) (Fr fβ cβ)


-- One-step reduction (proof of Theorem 6)
data PReduce {var : Ty β Set} :
             {Οβ : Ty} β
             PExp[ var ] Οβ β PExp[ var ] Οβ β Set where
  RBeta     : {Ο Οβ : Ty}
              {e : var Ο β PExp[ var ] Οβ}
              {v : Val[ var ] Ο}
              {e' : PExp[ var ] Οβ} β
              SubstPExp e v e' β
              PReduce (PApp (Val (PAbs e)) (Val v)) e'
             
  RPlus     : {nβ nβ : β} β
              PReduce (PPlus (Val (Num nβ)) (Val (Num nβ)))
                      (Val (Num (nβ + nβ)))

  RIs0      : {n : β} β
              PReduce (PIs0 (Val (Num n))) (Val (Bol (is0 n)))

  RB2S      : {b : πΉ} β
              PReduce (PB2S (Val (Bol b))) (Val (Str (b2s b)))

  RPrompt  : {Ο : Ty} β
              {vβ : Val[ var ] Ο} β
              PReduce (Prompt refl (Exp (Val vβ))) (Val vβ)

  RPControl : {Ο Ξ± Ξ² Ξ³ Ξ³' : Ty}
              {ΞΌα΅’ : Tr} β
              (p : pPCxt[ var , Ο ] Ξ±) β
              (xβ : id-cont-type Ξ³ ΞΌα΅’ Ξ³') β
              (e : var (Ο βp Ξ±) β
                   IExp[ var ] Ξ³ β¨ ΞΌα΅’ β© Ξ³' β¨ β β© Ξ²) β
              PReduce (Prompt refl (pPCxt-plugI p (PControl xβ e)))
                      (Prompt xβ (IApp (Exp (Val (IAbs e)))
                        (Exp (Val (PAbs (Ξ» x β pPCxt-plug p (Val (Var x))))))))

  RIControl : {Ο Ξ± Ξ±' Ξ² Ξ²' Ξ³ Ξ³' tβ tβ Οβ Οβ : Ty}
              {ΞΌβ ΞΌβ ΞΌα΅’ ΞΌΞ± ΞΌΞ±' ΞΌΞ² ΞΌΞ²' ΞΌβ ΞΌβ : Tr} β
              (pβ : pICxt[ var , Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ]
                         Οβ β¨ ΞΌβ β© Οβ β¨ β β© Ξ²) β
              (pβ : pICxt[ var , Ο β¨ ΞΌΞ±' β© Ξ±' β¨ ΞΌΞ±' β© Ξ±' ]
                         tβ β¨ ΞΌβ β© tβ β¨ ΞΌβ β© Ξ±) β
              {xβ : id-cont-type Οβ ΞΌβ Οβ} β
              (xβ : id-cont-type Ξ³ ΞΌα΅’ Ξ³') β
              (xβ : compatible (tβ ββ¨ ΞΌβ β© tβ) ΞΌβ ΞΌβ) β
              (xβ : compatible ΞΌΞ² ΞΌβ ΞΌΞ±) β
              same-pICxt pβ pβ β
              (e : var (Ο βi tβ β¨ ΞΌβ β© tβ β¨ ΞΌβ β© Ξ±) β
                   IExp[ var ] Ξ³ β¨ ΞΌα΅’ β© Ξ³' β¨ β β© Ξ²) β
              PReduce (Prompt xβ (pICxt-plug pβ (IControl xβ xβ xβ e)))
                      (Prompt xβ (IApp (Exp (Val (IAbs e)))
                        (Exp (Val (IAbs (Ξ» x β pICxt-plug pβ (Exp (Val (Var x)))))))))
                        
  RFr      : {Οβ Οβ : Ty}
             {e e' : PExp[ var ] Οβ} β
             (f : PFr[ var , Οβ ] Οβ) β
             PReduce e e' β
             PReduce (PFr-plug f e) (PFr-plug f e')
                     
data IReduce {var : Ty β Set} :
             {Ο Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
             IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² β
             IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² β Set where
  RExp   : {Ο Ξ± : Ty} {ΞΌΞ± : Tr} β
           {e e' : PExp[ var ] Ο} β
           PReduce e e' β IReduce {Ξ± = Ξ±} {ΞΌΞ± = ΞΌΞ±} (Exp e) (Exp e')

  RBeta  : {Οβ Οβ Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr}
           {e : var Οβ β IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²}
           {v : Val[ var ] Οβ}
           {e' : IExp[ var ] Οβ β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²} β
           SubstIExp e v e' β
           IReduce (IApp (Exp (Val (IAbs e))) (Exp (Val v))) e'

  RPBeta : {Οβ Οβ Ξ± Ξ² : Ty} {ΞΌΞ± : Tr}
           {e : var Οβ β PExp[ var ] Οβ}
           {v : Val[ var ] Οβ}
           {e' : PExp[ var ] Οβ} β
           SubstPExp e v e' β
           IReduce {Ξ± = Ξ±} {ΞΌΞ± = ΞΌΞ±}
                   (PIApp (Exp (Val (PAbs e))) (Exp (Val v))) (Exp e')

  RPlus  : {Ξ± : Ty} {ΞΌΞ± : Tr} {nβ nβ : β} β
           IReduce {Ξ± = Ξ±} {ΞΌΞ± = ΞΌΞ±}
                   (IPlus (Exp (Val (Num nβ))) (Exp (Val (Num nβ))))
                   (Exp (Val (Num (nβ + nβ))))

  RIs0   : {Ξ± : Ty} {ΞΌΞ± : Tr} {n : β} β
           IReduce {Ξ± = Ξ±} {ΞΌΞ± = ΞΌΞ±}
                   (IIs0 (Exp (Val (Num n)))) (Exp (Val (Bol (is0 n))))

  RB2S   : {Ξ± : Ty} {ΞΌΞ± : Tr} {b : πΉ} β
           IReduce {Ξ± = Ξ±} {ΞΌΞ± = ΞΌΞ±}
                   (IB2S (Exp (Val (Bol b)))) (Exp (Val (Str (b2s b))))         

  RFr    : {Ο Ξ± Ξ² Ο' Ξ±' Ξ²' : Ty} {ΞΌΞ± ΞΌΞ² ΞΌΞ±' ΞΌΞ²' : Tr}
           {e e' : IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²} β
           (f : IFr[ var , Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² ]
                   Ο' β¨ ΞΌΞ±' β© Ξ±' β¨ ΞΌΞ²' β© Ξ²') β
           IReduce e e' β
           IReduce (IFr-plug f e) (IFr-plug f e')


-- Multi-step reduction
data IReduce* {var : Ty β Set} :
              {Ο Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
              IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² β
              IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ² β Set where

  R*Id    : {Ο Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
            (e : IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β
            IReduce* e e
            
  R*Trans : {Ο Ξ± Ξ² : Ty} {ΞΌΞ± ΞΌΞ² : Tr} β
            (eβ : IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β
            (eβ : IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β
            (eβ : IExp[ var ] Ο β¨ ΞΌΞ± β© Ξ± β¨ ΞΌΞ² β© Ξ²) β
            IReduce eβ eβ β
            IReduce* eβ eβ β
            IReduce* eβ eβ
