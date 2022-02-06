-- Doodlings, re: Conal's "Simple Essence of Automatic Differentiation"
-- by David Banas <capn.freako@gmail.com>

module simple_essence where

open import Agda.Primitive
open import Data.Bool
open import Data.Float

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import plfa_local.part1.Isomorphism

ℜ = Float

postulate
  distrib : {m a b : ℜ} → m * (a + b) ≡ (m * a) + (m * b)
  assoc   : {a b c : ℜ} → a * (b * c) ≡ (a * b) * c
  commut  : {a b   : ℜ} → a * b       ≡ b * a
  
-----------------
-- Additive Types
-----------------
record Additive (A : Set) : Set where
  infixr 6 _⊕_
  field
    _⊕_ : A → A → A
open Additive ⦃ ... ⦄

instance
  RealAdditive : Additive ℜ
  RealAdditive = record { _⊕_ = _+_ }
  
-----------------
-- Scalable Types
-----------------
record Scalable (A : Set) : Set where
  infixr 7 _⊛_
  field
    _⊛_ : ℜ → A → A
open Scalable ⦃ ... ⦄

instance
  RealScalable : Scalable ℜ
  RealScalable = record { _⊛_ = _*_ }
  
-------------------
-- Linear Functions
-------------------
record Linear {A B : Set}
              {{_ : Additive A}} {{_ : Additive B}} {{_ : Scalable A}} {{_ : Scalable B}}
              (f : A → B) : Set where
  field
    adds   : ∀ (a b : A)
             ----------------------
           → f (a ⊕ b) ≡ f a ⊕ f b

    scales : ∀ (s : ℜ) (a : A)
             --------------------
           → f (s ⊛ a) ≡ s ⊛ f a

open Linear ⦃ ... ⦄

line : ℜ → ℜ → ℜ
line m = λ x → m * x

instance
  LinMap : {m : ℜ} → Linear (line m)
  LinMap {m} = record
    { adds =
        λ { a b →
              begin
                line m (a ⊕ b)
              ≡⟨ cong (line m) refl ⟩
                line m (a + b)
              ≡⟨⟩
                (m * (a + b))
              ≡⟨ distrib {m = m} ⟩
                ((m * a) + (m * b))
              ≡⟨⟩
                ((m * a) ⊕ (m * b))
              ≡⟨⟩
                ((line m a) ⊕ (line m b))
              ∎
          }
    ; scales =
        λ { s a →
              begin
                line m (s ⊛ a)
              ≡⟨⟩
                line m (s * a)
              ≡⟨⟩
                m * (s * a)
              ≡⟨ assoc {m} ⟩
                (m * s) * a
              ≡⟨ cong (_* a) (commut {m} {s}) ⟩
                (s * m) * a
              ≡⟨ sym (assoc {s}) ⟩
                s * (m * a)
              ≡⟨⟩
                s * (line m a)
              ≡⟨⟩
                s ⊛ (line m a)
              ∎
          }
    }
  
------------------------------
-- Continuation of Linear Maps
------------------------------
record LinCont {A B : Set} (f : B → ℜ)
               ⦃ _ : Additive B ⦄ ⦃ _ : Scalable B ⦄ ⦃ _ : Linear f ⦄
               : Set where
  field
    priv : A → B
  cont : A → ℜ
  cont = f ∘ priv

-- ---------------
-- -- Isomorphisms
-- ---------------

-- -- Linear mapping of scalars
-- s⊸s≃s : {m : ℜ}
--         ------------
--       -- → LinMap {m} ≃ ℜ
--       → {!!} ≃ ℜ
-- s⊸s≃s = record
--   { to = λ {lm → {!!}}
--   ; from = λ {x → record { adds = {!!} ; scales = {!!} }}
--   ; from∘to = {!!}
--   ; to∘from = {!!}
--   }
      
-- -- a⊸ℜ≃a : ∀ {A : Set} {f : A → ℜ}
-- --         -----------------------
-- --       → Linear f ≃ A
-- -- a⊸ℜ≃a = record
-- --   { to = λ {x → {!!}}
-- --   ; from = {!!}
-- --   ; from∘to = {!!}
-- --   ; to∘from = {!!}
-- --   }

