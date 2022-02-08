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

ℜ     = Float

-- These aren't strictly true for machine types approximating real
-- (i.e. - `Float`, etc.), but that's okay for our "demo" purposes here.
postulate
  distrib : {m a b : ℜ} → m * (a + b) ≡ (m * a) + (m * b)
  assoc   : {a b c : ℜ} → a * (b * c) ≡ (a * b) * c
  commut  : {a b   : ℜ} → a * b       ≡ b * a

----------------------------------------------------------------------
-- Scalar Values
--
-- Because `_≃_` won't accept ℜ; it requires something with type: Set.
-- So, we wrap up a ℜ inside a § constructor, to fulfill that need.
----------------------------------------------------------------------
record Scalar : Set where
  constructor § 
  field
    val : ℜ
open Scalar ⦃ ... ⦄

add§ : Scalar → Scalar → Scalar
add§ (§ x) (§ y) = § (x + y)
  
mul§ : ℜ → Scalar → Scalar
mul§ x (§ y) = § (x * y)

------------------------------------------------------------------------
-- Composite Values (i.e. - some assemblage of scalars)
--
-- We purposefully remain as vague as possible about the exact nature of
-- the assemblage, preferring to capture whatever truisms are available
-- to us in their most general/abstract form.
------------------------------------------------------------------------

-----------------
-- Additive Types
-----------------
record Additive (A : Set) : Set where
  infixl 6 _⊕_  -- Just matching associativity/priority of `_+_`.
  field
    _⊕_ : A → A → A
open Additive ⦃ ... ⦄

instance
  RealAdditive : Additive ℜ
  RealAdditive = record { _⊕_ = _+_ }

  ScalarAdditive : Additive Scalar
  ScalarAdditive = record { _⊕_ = add§ }
  
-----------------
-- Scalable Types
-----------------
record Scalable (A : Set) : Set where
  infixl 7 _⊛_
  field
    _⊛_ : ℜ → A → A
open Scalable ⦃ ... ⦄

instance
  RealScalable : Scalable ℜ
  RealScalable = record { _⊛_ = _*_ }

  ScalarScalable : Scalable Scalar
  ScalarScalable = record { _⊛_ = mul§ }
  
--------------
-- Linear Maps
--------------
record LinMap {A B : Set}
              {{_ : Additive A}} {{_ : Additive B}}
              {{_ : Scalable A}} {{_ : Scalable B}}
              : Set where
  field
    f      : A → B
    
    adds   : ∀ (a b : A)
             ----------------------
           → f (a ⊕ b) ≡ f a ⊕ f b

    scales : ∀ (s : ℜ) (a : A)
             --------------------
           → f (s ⊛ a) ≡ s ⊛ f a

open LinMap ⦃ ... ⦄

scalar-map : ℜ → LinMap {ℜ} {ℜ}
scalar-map m = record
  { f      = m *_
  ; adds   = λ a b → distrib {m} {a} {b}
  ; scales =
      λ { s a → begin
                  m * (s * a)
                ≡⟨ assoc {m} ⟩
                  (m * s) * a
                ≡⟨ cong (_* a) (commut {m} {s}) ⟩
                  (s * m) * a
                ≡⟨ sym (assoc {s}) ⟩
                  s * (m * a)
                ∎
        }
  }

-- To accommodate `_≃_`, which doesn't accept ℜ directly.
record ScalarMap : Set where
  field
    m : ℜ
  map : LinMap {ℜ} {ℜ}
  map = scalar-map m
  
------------------------------
-- Continuation of Linear Maps
------------------------------
-- record LinCont {A B : Set} (f : B → ℜ)
--                ⦃ _ : Additive B ⦄ ⦃ _ : Scalable B ⦄ ⦃ _ : Linear ⦄
-- record LinCont {A B : Set} (LinMap {B} {ℜ}) : Set where
-- record LinCont {A B : Set} : Set where
-- -- record LinCont : {A B : Set} (LinMap {B} {ℜ}) → Set where
--   field
--     priv : A → B
--     objM : LinMap {B} {ℜ}
--   -- cont : A → ℜ
--   -- cont = f ∘ priv
--   cont : LinMap {A} {ℜ}
--   cont = record
--     { f = (f objM) ∘ priv
--     ; adds = ?
--     ; scales = ?
--     }

---------------
-- Isomorphisms
---------------

-- Linear mapping of scalars: s ⊸ s ≃ s
--
-- The slope of a line completely determines a mapping between scalars,
-- when that mapping is linear.
-- (Note that such a mapping must pass through the origin.)
s⊸s≃s : ScalarMap ≃ Scalar
s⊸s≃s =
  record { to = § ∘ ScalarMap.m
         ; from = λ (§ m) → record { m = m }
         ; from∘to = λ {x → refl}
         ; to∘from = λ {y → refl}
         }

-- Linear mapping of composite types to scalars: a ⊸ s ≃ a
--
-- Because the constructions we use to form composite types (i.e. - vectors)
-- are linear operators themselves, we can show that linear maps from these
-- types to a scalar are isomorphic to the type itself, where each element
-- contains the slope used to map the value of that element, in some hypothetical
-- input vector, to its (additive) contribution to the final value `s`.
-- -- -- a⊸ℜ≃a : ∀ {A : Set} {f : A → ℜ}
-- -- --         -----------------------
-- -- --       → Linear f ≃ A
-- -- -- a⊸ℜ≃a = record
-- -- --   { to = λ {x → {!!}}
-- -- --   ; from = {!!}
-- -- --   ; from∘to = {!!}
-- -- --   ; to∘from = {!!}
-- -- --   }

