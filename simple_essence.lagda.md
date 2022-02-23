---
title: Agda Doodlings by Dave
...

# Agda Doodlings, re: Conal's "Simple Essence of Automatic Differentiation"

by: David Banas <capn.freako@gmail.com>  
on: February 19, 2022

In this [literate Agda](https://agda.readthedocs.io/en/v2.6.2.1/tools/literate-programming.html#literate-markdown) file I'm exploring some of the ideas written about by Conal Elliott in his paper: _The Simple Essence of Automatic Differentiation_.
In particular, I'm attempting to prove, using Agda, some of the isomorphisms that Conal reveals in that paper.

## Preliminaries

Here I define my Agda module and import what it needs from the standard library.

```agda
module simple_essence where

open import Agda.Primitive
open import Data.Bool
open import Data.Float

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import plfa_local.part1.Isomorphism  -- ToDo: Replace w/ equivalent from standard library.

```

## Types

In the following subsections I define the types used in my proofs, below.

### Real Proxy and Necessary Postulates

Here I define `Float` as my proxy for real numbers and provide some basic postulates, which are required for my subsequent proofs, but not strictly true for type `Float`.

**ToDo**: Eliminate this, as per Conal's advice, and predicate everything on `Semiring`, instead.

```agda
ℜ = Float

-- These aren't strictly true for machine types approximating real
-- (i.e. - `Float`, etc.), but that's okay for our "demo" purposes here.
postulate
  distrib  : {m a b : ℜ} → m * (a + b) ≡ (m * a) + (m * b)
  assoc-*  : {a b c : ℜ} → (a * b) * c ≡ a * (b * c)
  commut-* : {a b   : ℜ} → a * b       ≡ b * a
  assoc-+  : {a b c : ℜ} → (a + b) + c ≡ a + (b + c)
  commut-+ : {a b   : ℜ} → a + b       ≡ b + a

```

### Composite Values (i.e. - some assemblage of scalars)

**Note:** This is a first failed attempt at a composite type, which I leave in for reference and (hopefully) interesting discussion.
The snag I hit was the `Additive` instance didn't terminate, due to there being no information regarding a term's "depth" in the type.
(See the *Additive Types* section, below.)

Here I define my general *term* type, which can be either:

- a scalar, or

- a product of two terms.

In this way, we're able to build any arbitrarily shaped tensor over the field of reals.
Or, perhaps more precisely, we can build structures that are _isomorphic_ to any arbitrarily shaped tensor.
We can't actually build a triple using this machinery, for instance.
But, `((x, y), z)` contains the same information as `(x, y, z)`, even including term positioning.

    infixl 5 _,_
    data Term : Set where
      σ   : ℜ → Term
      _,_ : ∀ (A B : Term) → Term

### Scalar Values

Here I define my basic *scalar* type.
The *isomorphism* operator: `_≃_`, won't accept ℜ; it requires something with type: `Set`.
So, we wrap up a ℜ inside a § constructor, to fulfill that need.

```agda
data Scalar : Set where
  § : ℜ → Scalar

```

#### Scalar Addition

Scalar addition is defined by requiring that a sum of scalars is a scalar of the sum.

```agda
infixl 6 _+§_  -- Just using the associativity/priority of ordinary addition.
_+§_ : Scalar → Scalar → Scalar
(§ x) +§ (§ y) = § (x + y)

```

We can show that it is both *associative* and *commutative*, thanks to the associativity and commutativity of the underlying real field upon which it depends.

```agda
assoc-+§ : (x y z : Scalar)
           -----------------------------
         → (x +§ y) +§ z ≡ x +§ (y +§ z)
assoc-+§ (§ x) (§ y) (§ z) =
  begin
    ((§ x) +§ (§ y)) +§ (§ z)
  ≡⟨⟩
    (§ (x + y)) +§ (§ z)
  ≡⟨⟩
    § ((x + y) + z)
  ≡⟨ cong § (assoc-+ {x}) ⟩
    § (x + (y + z))
  ≡⟨⟩
    (§ x) +§ (§ (y + z))
  ≡⟨⟩
    (§ x) +§ ((§ y) +§ (§ z))
  ∎

commut-+§ : (x y : Scalar)
            ---------------
          → x +§ y ≡ y +§ x
commut-+§ (§ x) (§ y) =
  begin
    (§ x) +§ (§ y)
  ≡⟨⟩
    § (x + y)
  ≡⟨ cong § (commut-+ {x}) ⟩
    § (y + x)
  ≡⟨⟩
    (§ y) +§ (§ x)
  ∎

```

#### Scalar Multiplication by Real

Again, we simply require the operator to be an endofunctor.
And we can show distributivity.

```agda
infixl 7 _*§_
_*§_ : ℜ → Scalar → Scalar
x *§ (§ y) = § (x * y)

distrib-*§ : (s : ℜ) → (x y : Scalar)
             --------------------------------
           → s *§ (x +§ y) ≡ s *§ x +§ s *§ y
distrib-*§ s (§ x) (§ y) =
  begin
    s *§ (§ x +§ § y)
  ≡⟨⟩
    s *§ § (x + y)
  ≡⟨⟩
    § (s * (x + y))
  ≡⟨ cong § (distrib {s}) ⟩
    § ((s * x) + (s * y))
  ≡⟨⟩
    § (s * x) +§ § (s * y)
  ≡⟨⟩
    s *§ (§ x) +§ s *§ (§ y)
  ∎

```

### Pairs

I use *nonuniform* pairs, to allow for maximum flexibility in assembling composite types.
I also provide the "cross" operator from Conal's paper, in both unary and binary form.

```agda
infixl 5 _,_
data Pair (A B : Set) : Set where
  _,_ : (x : A) → (y : B) → Pair A B

_Χ_ : {A B C D : Set} → (A → C) → (B → D) → Pair A B → Pair C D
f Χ g = λ {(x , y) → ((f x) , (g y))}

_Χ₂_ : {A B C D E F : Set} → (A → C → E) → (B → D → F) → Pair A B → Pair C D → Pair E F
f Χ₂ g = λ {(x , y) (w , z) → ((f x w) , (g y z))}

```

## Type Classes

Here I define some classes of types with useful common properties.

### Additive Types

The type class `Additive` just requires an *associative* binary joining operator, which accepts two arguments within the type and produces a result also within the type.
In order to be a member of this class, _all_ elements of the candidate type must be suitable as inputs (in either position) to this joining operator.

```agda
record Additive (A : Set) : Set where
  infixl 6 _⊕_  -- Just matching associativity/priority of `_+_`.
  field
    _⊕_ : A → A → A
    assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
open Additive {{ ... }}

```

All of our previously defined types, except `Term`,  have `Additive` instances:

```agda
instance
  RealAdditive : Additive ℜ
  RealAdditive = record
    { _⊕_     = _+_
    ; assoc-⊕ = λ {x y z → assoc-+ {x} {y} {z}}
    }

  ScalarAdditive : Additive Scalar
  ScalarAdditive = record
    { _⊕_ = _+§_
    ; assoc-⊕ = λ {x y z → assoc-+§ x y z}
    }

  -- ToDo: Review paper, to determine proper spec. for this implementation.
  PairAdditive : {A B : Set} {{_ : Additive A}} {{_ : Additive B}}
               → Additive (Pair A B)
  PairAdditive = record
    { _⊕_ = (_⊕_ Χ₂ _⊕_)
    ; assoc-⊕ =
        λ { (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) →
              begin
                (x₁ ⊕ y₁ ⊕ z₁   , x₂ ⊕ y₂ ⊕ z₂)
              ≡⟨ cong (_, x₂ ⊕ y₂ ⊕ z₂) (assoc-⊕ x₁ y₁ z₁) ⟩
                (x₁ ⊕ (y₁ ⊕ z₁) , x₂ ⊕ y₂ ⊕ z₂)
              ≡⟨ cong (x₁ ⊕ (y₁ ⊕ z₁) ,_) (assoc-⊕ x₂ y₂ z₂) ⟩
                (x₁ ⊕ (y₁ ⊕ z₁) , x₂ ⊕ (y₂ ⊕ z₂))
              ∎
          }
    }

  -- TermAdditive : Additive Term
  -- TermAdditive = record
  --   { _⊕_ =
  --     λ { (σ x) (σ y)         → σ (x + y)
  --       ; (σ x) (y₁ , y₂)     → σ x ⊕ y₁ , σ x ⊕ y₂
  --       ; (x₁ , x₂) (σ y)     → {!!}
  --       ; (x₁ , x₂) (y₁ , y₂) → {!!}}
  --   ; assoc-⊕ = {!!}
  --   }

```

**Notes:**

1. Despite the perhaps obvious nature of these instances, it'd be nice to _specify_ them first, ala Conal, and then *derive* the code above from that specification.

    - [ ] Review instance implementation derivation from homomorphic specification, in Conal's paper, and apply above.

1. The (failed) `TermAdditive` instance, above, had two issues:

    1. It didn't terminate.
    
    1. I arbitrarily chose to "broadcast" in the case of a scalar being added to a "vector".
    
        - What is the justification for making this choice?
        
        - Would it have satisfied the axioms of linearity?

### Scalable Types

This class defines a binary scaling operator taking one real value and one member of the type, producing an element of the type as its output.
In order to be a member of this class any member of the type must be combinable with any real value, via the scaling operator, producing a result also within the type.

```agda
record Scalable (A : Set) : Set where
  infixl 7 _⊛_
  field
    _⊛_ : ℜ → A → A
open Scalable {{ ... }}
```

Again, all of our previously defined types, except `Term`, have instances:

```agda
instance
  RealScalable : Scalable ℜ
  RealScalable = record { _⊛_ = _*_ }

  ScalarScalable : Scalable Scalar
  ScalarScalable = record { _⊛_ = _*§_ }
  
  -- ToDo: Review paper, to determine proper spec. for this implementation.
  PairScalable : {A B : Set} {{_ : Scalable A}} {{_ : Scalable B}} → Scalable (Pair A B)
  PairScalable = record { _⊛_ = λ m → (m ⊛_) Χ (m ⊛_) }

```

### Linear Maps

This class captures the meaning of _linearity_.
The class considers a function to be linear if it (as Conal notes in his paper) distributes over addition and scaling.

```agda
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

open LinMap {{ ... }}

```

#### Linear Scalar Map

Here is a linear map between scalars.
It is simply a line in the xy-plane translating x-coordinate inputs to y-coordinate outputs.
Since it must pass through the origin, in order to be linear, it is defined by a single quantity: its *slope*, which I refer to in the code as `m`, following what I learned in high school trigonometry class.

```agda
scalar-map : ℜ → LinMap {ℜ} {ℜ}
scalar-map m = record
  { f      = m *_
  ; adds   = λ a b → distrib {m} {a} {b}
  ; scales =
      λ { s a → begin
                  m * (s * a)
                ≡⟨ sym (assoc-* {m}) ⟩
                  (m * s) * a
                ≡⟨ cong (_* a) (commut-* {m} {s}) ⟩
                  (s * m) * a
                ≡⟨ assoc-* {s} ⟩
                  s * (m * a)
                ∎
        }
  }

-- To accommodate `_≃_`, which only accepts arguments of type `Set`.
record ScalarMap : Set where
  field
    m : ℜ
  map : LinMap {ℜ} {ℜ}
  map = scalar-map m

```

#### Linear Map from Pair of Scalars to Scalar

**Note:** I've arbitrarily chosen to _sum_ the partial products, in order to form the final result.
I might have, instead, taken their product.
What justifies this choice?

```agda
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
                 ≡⟨ sym (assoc-+ {(m₁ * x) + (m₁ * x₁)} {(m₂ * y)} {(m₂ * y₁)}) ⟩
                   (((m₁ * x) + (m₁ * x₁)) + (m₂ * y)) + (m₂ * y₁)
                 ≡⟨ cong (_+ (m₂ * y₁)) (assoc-+ {(m₁ * x)} {(m₁ * x₁)} {(m₂ * y)}) ⟩
                   ((m₁ * x) + ((m₁ * x₁) + (m₂ * y))) + (m₂ * y₁)
                 ≡⟨ sym (sym (assoc-+ {m₁ * x} {(m₁ * x₁) + (m₂ * y)} {m₂ * y₁})) ⟩
                   (m₁ * x) + (((m₁ * x₁) + (m₂ * y)) + (m₂ * y₁))
                 ≡⟨ cong ((m₁ * x) +_) (cong (_+ (m₂ * y₁)) (commut-+ {m₁ * x₁} {m₂ * y})) ⟩
                   (m₁ * x) + (((m₂ * y) + (m₁ * x₁)) + (m₂ * y₁))
                 ≡⟨ cong ((m₁ * x) +_) (sym (sym (assoc-+ {m₂ * y} {m₁ * x₁} {m₂ * y₁}))) ⟩
                   (m₁ * x) + ((m₂ * y) + ((m₁ * x₁) + (m₂ * y₁)))
                 ≡⟨ sym (assoc-+ {m₁ * x} {m₂ * y} {(m₁ * x₁) + (m₂ * y₁)}) ⟩
                   ((m₁ * x) + (m₂ * y)) + ((m₁ * x₁) + (m₂ * y₁))
                 ∎
             }
  ; scales = λ { s (x , y) →
                   begin
                     (m₁ * (s * x)) + (m₂ * (s * y))
                   ≡⟨ cong (_+ (m₂ * (s * y))) (sym (assoc-* {m₁} {s} {x})) ⟩
                     ((m₁ * s) * x) + (m₂ * (s * y))
                   ≡⟨ cong (_+ (m₂ * (s * y))) (cong (_* x) (commut-* {m₁} {s})) ⟩
                     ((s * m₁) * x) + (m₂ * (s * y))
                   ≡⟨ cong (_+ (m₂ * (s * y))) (assoc-* {s} {m₁} {x}) ⟩
                     (s * (m₁ * x)) + (m₂ * (s * y))
                   ≡⟨ cong ((s * (m₁ * x)) +_) (sym (assoc-* {m₂} {s} {y})) ⟩
                     (s * (m₁ * x)) + ((m₂ * s) * y)
                   ≡⟨ cong ((s * (m₁ * x)) +_) (cong (_* y) (commut-* {m₂} {s})) ⟩
                     (s * (m₁ * x)) + ((s * m₂) * y)
                   ≡⟨ cong ((s * (m₁ * x)) +_) (sym (sym (assoc-* {s} {m₂} {y}))) ⟩
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

```

#### Linear Map from Arbitrary Non-uniform Pair to Scalar

This ought to be the last prerequisite necessary before attempting to prove Conal's isomorphism: $a \mapsto \Re \cong a$.

```agda
-- vec-map : {A B : Set}
--           {{_ : Additive A}} {{_ : Additive B}}
--           {{_ : Scalable A}} {{_ : Scalable B}}
--         → Pair A B → LinMap (Pair A B) ℜ

```

```agda
-- ------------------------------
-- -- Continuation of Linear Maps
-- ------------------------------
-- -- record LinCont {A B : Set} (f : B → ℜ)
-- --                ⦃ _ : Additive B ⦄ ⦃ _ : Scalable B ⦄ ⦃ _ : Linear ⦄
-- -- record LinCont {A B : Set} (LinMap {B} {ℜ}) : Set where
-- -- record LinCont {A B : Set} : Set where
-- -- -- record LinCont : {A B : Set} (LinMap {B} {ℜ}) → Set where
-- --   field
-- --     priv : A → B
-- --     objM : LinMap {B} {ℜ}
-- --   -- cont : A → ℜ
-- --   -- cont = f ∘ priv
-- --   cont : LinMap {A} {ℜ}
-- --   cont = record
-- --     { f = (f objM) ∘ priv
-- --     ; adds = ?
-- --     ; scales = ?
-- --     }

```

## Isomorphisms

Here I attempt to prove certain *isomorphisms* revealed by Conal in his paper.

```agda
-- -- Linear mapping of scalars: s ⊸ s ≃ s
-- --
-- -- The slope of a line completely determines a mapping between scalars,
-- -- when that mapping is linear.
-- -- (Note that such a mapping must pass through the origin.)
-- s⊸s≃s : ScalarMap ≃ Scalar
-- s⊸s≃s =
--   record { to      = § ∘ ScalarMap.m
--          ; from    = λ { (§ m) → record { m = m } }
--          ; from∘to = λ { x     → refl }
--          ; to∘from = λ { (§ m) → refl }
--          }

```

### Linear mapping of composite types to scalars: a ⊸ s ≃ a

Because the constructions we use to form composite types (i.e. - vectors)
are linear operators themselves, we can show that linear maps from these
types to a scalar are isomorphic to the type itself, where each element
contains the slope used to map the value of that element, in some hypothetical
input vector, to its (additive) contribution to the final value `s`.

```agda
-- a⊸ℜ≃a : ∀ {A : Set} {{_ : Additive A}} {{_ : Scalable A}}
--         --------------
--       → LinMap {A} {ℜ} ≃ A
-- a⊸ℜ≃a = record
--   { to = λ { lm → {!!} }
--     -- Strategy: Perform N applications of lm.f, where N is the "size" of A.
--     -- Give each application a different "basis vector" of A (i.e. - a
--     -- value of type: A, which contains only one non-zero element: '1') and
--     -- store the result in the returned value at the position corresponding
--     -- to the single non-zero element in this particular basis vector.
--     -- Requires: {{Representable A}}
--   ; from = λ { m → {!!} }
--     -- Strategy: Build a LinMap record where `f` takes the dot product of its
--     -- input w/ `m`.
--     -- Requires: {{Zippable A}} (Do we get that for free from Representable?)
--   ; from∘to = {!!}
--   ; to∘from = {!!}
--   }

```
