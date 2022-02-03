-- Doodlings, re: Conal's "Simple Essence of Automatic Differentiation"
-- by David Banas <capn.freako@gmail.com>

module simple_essence where

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_)
open import Agda.Primitive
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import plfa_local.part1.Isomorphism

postulate ℜ : Set
{-# BUILTIN FLOAT ℜ #-}

-----------------
-- Additive Types
-----------------
record Additive (A : Set) : Set where
  field
    add : A → A → A
open Additive
_+_ : ∀ {A : Set} {{addA : Additive A}} → A → A → A
_+_ {{addA}} x y = add addA x y
infixr 5 _+_

-----------------
-- Scalable Types
-----------------
record Scalable (A : Set) : Set where
  field
    mult : ℜ → A → A
open Scalable
_*_ : ∀ {A : Set} {{scalA : Scalable A}} → ℜ → A → A
_*_ {{scalA}} s x = mult scalA s x
infixr 6 _*_

-------------------
-- Linear Functions
-------------------
record Linear {A B : Set} (f : A → B) : Set where
  field
    adds   : {{_ : Additive A}} {{_ : Additive B}}
           → ∀ {a b : A}
             ---------------------
           → f (a + b) ≡ f a + f b

    scales : {{_ : Scalable A}} {{_ : Scalable B}}
           → ∀ (s : ℜ) (a : A)
             -------------------
           → f (s * a) ≡ s * f a

------------------------------
-- Continuation of Linear Maps
------------------------------
record LinCont {A B : Set} (f : B → ℜ) : Set where
  field
    priv : A → B
  cont : {{_ : Linear f}} → A → ℜ
  cont = f ∘ priv

---------------
-- Isomorphisms
---------------

-- Linear mapping of scalars
s⊸s≃s : ∀ {f : ℜ → ℜ}
        ------------
      → Linear f ≃ ℜ
s⊸s≃s = record
  { to = λ {x → {!!}}
  ; from = {!!}
  ; from∘to = {!!}
  ; to∘from = {!!}
  }
      
-- a⊸ℜ≃a : ∀ {A : Set} {f : A → ℜ}
--         -----------------------
--       → Linear f ≃ A
-- a⊸ℜ≃a = record
--   { to = λ {x → {!!}}
--   ; from = {!!}
--   ; from∘to = {!!}
--   ; to∘from = {!!}
--   }

