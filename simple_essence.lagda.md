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

-- These aren't strictly true for machine types approximating real
-- (i.e. - `Float`, etc.), but that's okay for our "demo" purposes here.
postulate
  distrib  : {m a b : ℜ} → m * (a + b) ≡ (m * a) + (m * b)
  assoc-*  : {a b c : ℜ} → a * (b * c) ≡ (a * b) * c
  commut-* : {a b   : ℜ} → a * b       ≡ b * a
  assoc-+  : {a b c : ℜ} → a + (b + c) ≡ (a + b) + c
  commut-+ : {a b   : ℜ} → a + b       ≡ b + a

----------------------------------------------------------------------
-- Scalar Values
--
-- Because `_≃_` won't accept ℜ; it requires something with type: Set.
-- So, we wrap up a ℜ inside a § constructor, to fulfill that need.
----------------------------------------------------------------------
data Scalar : Set where
  § : ℜ → Scalar

add§ : Scalar → Scalar → Scalar
add§ (§ x) (§ y) = § (x + y)
  
mul§ : ℜ → Scalar → Scalar
mul§ x (§ y) = § (x * y)

--------
-- Pairs
--------
data Pair (A B : Set) : Set where
  _,_ : (x : A) → (y : B) → Pair A B

_Χ_ : {A B C D : Set} → (A → C) → (B → D) → Pair A B → Pair C D
f Χ g = λ {(x , y) → ((f x) , (g y))}

_Χ₂_ : {A B C D E F : Set} → (A → C → E) → (B → D → F) → Pair A B → Pair C D → Pair E F
f Χ₂ g = λ {(x , y) (w , z) → ((f x w) , (g y z))}

------------------------------------------------------------------------
-- Composite Values (i.e. - some assemblage of scalars)
--
-- We purposefully remain as vague as possible about the exact nature of
-- the assemblage, preferring to capture whatever truisms are available
-- to us in their most general/abstract form.
------------------------------------------------------------------------
data Term : Set₁ where
  σ   : Scalar → Term
  _π_ : ∀ {A B : Set} → Pair A B → Term
  
-----------------
-- Additive Types
-----------------
record Additive (A : Set) : Set where
  infixl 6 _⊕_  -- Just matching assoc-*iativity/priority of `_+_`.
  field
    _⊕_ : A → A → A
open Additive ⦃ ... ⦄

instance
  RealAdditive : Additive ℜ
  RealAdditive = record { _⊕_ = _+_ }

  ScalarAdditive : Additive Scalar
  ScalarAdditive = record { _⊕_ = add§ }

  -- ToDo: Review paper, to determine proper spec. for this implementation.
  PairAdditive : {A B : Set} {{_ : Additive A}} {{_ : Additive B}} → Additive (Pair A B)
  PairAdditive = record { _⊕_ = (_⊕_ Χ₂ _⊕_) }
  
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
  
  -- ToDo: Review paper, to determine proper spec. for this implementation.
  PairScalable : {A B : Set} {{_ : Scalable A}} {{_ : Scalable B}} → Scalable (Pair A B)
  PairScalable = record { _⊛_ = λ m → (m ⊛_) Χ (m ⊛_) }
  
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
                ≡⟨ assoc-* {m} ⟩
                  (m * s) * a
                ≡⟨ cong (_* a) (commut-* {m} {s}) ⟩
                  (s * m) * a
                ≡⟨ sym (assoc-* {s}) ⟩
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

-- pair-map : {A B : Set}
--            {{_ : Additive A}} {{_ : Additive B}}
--            {{_ : Scalable A}} {{_ : Scalable B}}
pair-map : Pair ℜ ℜ → LinMap {Pair ℜ ℜ} {ℜ}
pair-map (m₁ , m₂) = record
  { f = λ { (x , y) → (m₁ * x) + (m₂ * y) }
  ; adds = λ { (x , y) (x₁ , y₁) →
                 begin
                   (m₁ * (x + x₁)) + (m₂ * (y + y₁))
                 ≡⟨ cong (_+ (m₂ * (y + y₁))) (distrib {m₁} {x} {x₁}) ⟩
                   ((m₁ * x) + (m₁ * x₁)) + (m₂ * (y + y₁))
                 ≡⟨ cong (((m₁ * x) + (m₁ * x₁)) +_) (distrib {m₂} {y} {y₁}) ⟩
                   ((m₁ * x) + (m₁ * x₁)) + ((m₂ * y) + (m₂ * y₁))
                 ≡⟨ assoc-+ {(m₁ * x) + (m₁ * x₁)} {(m₂ * y)} {(m₂ * y₁)} ⟩
                   (((m₁ * x) + (m₁ * x₁)) + (m₂ * y)) + (m₂ * y₁)
                 ≡⟨ cong (_+ (m₂ * y₁)) (sym (assoc-+ {(m₁ * x)} {(m₁ * x₁)} {(m₂ * y)})) ⟩
                   ((m₁ * x) + ((m₁ * x₁) + (m₂ * y))) + (m₂ * y₁)
                 ≡⟨ sym (assoc-+ {m₁ * x} {(m₁ * x₁) + (m₂ * y)} {m₂ * y₁}) ⟩
                   (m₁ * x) + (((m₁ * x₁) + (m₂ * y)) + (m₂ * y₁))
                 ≡⟨ cong ((m₁ * x) +_) (cong (_+ (m₂ * y₁)) (commut-+ {m₁ * x₁} {m₂ * y})) ⟩
                   (m₁ * x) + (((m₂ * y) + (m₁ * x₁)) + (m₂ * y₁))
                 ≡⟨ cong ((m₁ * x) +_) (sym (assoc-+ {m₂ * y} {m₁ * x₁} {m₂ * y₁})) ⟩
                   (m₁ * x) + ((m₂ * y) + ((m₁ * x₁) + (m₂ * y₁)))
                 ≡⟨ assoc-+ {m₁ * x} {m₂ * y} {(m₁ * x₁) + (m₂ * y₁)} ⟩
                   ((m₁ * x) + (m₂ * y)) + ((m₁ * x₁) + (m₂ * y₁))
                 ∎
             }
  ; scales = λ { s (x , y) →
                   begin
                     (m₁ * (s * x)) + (m₂ * (s * y))
                   ≡⟨ cong (_+ (m₂ * (s * y))) (assoc-* {m₁} {s} {x}) ⟩
                     ((m₁ * s) * x) + (m₂ * (s * y))
                   ≡⟨ cong (_+ (m₂ * (s * y))) (cong (_* x) (commut-* {m₁} {s})) ⟩
                     ((s * m₁) * x) + (m₂ * (s * y))
                   ≡⟨ cong (_+ (m₂ * (s * y))) (sym (assoc-* {s} {m₁} {x})) ⟩
                     (s * (m₁ * x)) + (m₂ * (s * y))
                   ≡⟨ cong ((s * (m₁ * x)) +_) (assoc-* {m₂} {s} {y}) ⟩
                     (s * (m₁ * x)) + ((m₂ * s) * y)
                   ≡⟨ cong ((s * (m₁ * x)) +_) (cong (_* y) (commut-* {m₂} {s})) ⟩
                     (s * (m₁ * x)) + ((s * m₂) * y)
                   ≡⟨ cong ((s * (m₁ * x)) +_) (sym (assoc-* {s} {m₂} {y})) ⟩
                     (s * (m₁ * x)) + (s * (m₂ * y))
                   ≡⟨ sym (distrib {s} {m₁ * x} {m₂ * y}) ⟩
                     s * ((m₁ * x) + (m₂ * y))
                   ∎
               }
  }

record PairMap : Set where
  field
    ms : Pair ℜ ℜ
  map : LinMap {Pair ℜ ℜ} {ℜ}
  map = pair-map ms

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
  record { to      = § ∘ ScalarMap.m
         ; from    = λ { (§ m) → record { m = m } }
         ; from∘to = λ { x     → refl }
         ; to∘from = λ { (§ m) → refl }
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

