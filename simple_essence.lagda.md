---
format: markdown
title: Agda Doodlings, re: Conal's "Simple Essence of Automatic Differentiation"
---

# Agda Doodlings, re: Conal's "Simple Essence of Automatic Differentiation"

by: David Banas <capn.freako@gmail.com>  
on: February 19, 2022

In this [literate Agda](https://agda.readthedocs.io/en/v2.6.2.1/tools/literate-programming.html#literate-markdown) file I'm exploring some of the ideas written about by Conal Elliott in his paper: _The Simple Essence of Automatic Differentiation_.
In particular, I'm attempting to prove, using Agda, some of the isomorphisms that Conal reveals in that paper.

## Introduction

In (re)reading Conal's paper, I noticed something that I thought was a typo:

> The internal representation of $Cont^{s}_{(⊸)} \, a \, b$ is $(b ⊸ s) → (a ⊸ s)$, which is isomorphic to $b → a$.

I thought for sure Conal meant to say:

> ... isomorphic to $a → b$.

since the continuation must "know" how to get from `a` to `b`, in order to offer the type signature it does.
(Can this be proven in Agda, perhaps by using a proof-by-contradiction approach?)

But, when I discussed this with Conal, he drew my attention to the paragraph immediately above, in which he points out:

> In particular, every linear map in $A ⊸ s$ has the form `dot u` for some `u :: A`,

And that, therefore, since $a ⊸ s$ is isomorphic to $a$,  $(b ⊸ s) → (a ⊸ s)$ is indeed isomorphic to $b → a$.

Well, that's very interesting, because now we've got something (the _continuation_) that is isomorphic to both $a → b$ and $b → a$.
And, because the isomorphism relation is _transitive_, that means: $a → b ≅ b → a$!
Of course, this only holds in the special case where both types $a$ and $b$ have linear maps to the underlying scalar field.
And the existence of this duality under this very special condition is sort of the punchline of Conal's paper.
Nevertheless, it struck me as quite powerful to be able to prove, at the outset and using Agda, that the duality must exist.

## Preliminaries

First, we need to codify in Agda what we mean by a _linear map_.
We'll take Conal's definition: a linear map is...

> a function that distributes over tensor addition and scalar multiplication.

That is:

$$
f : A \to B
$$

and:

$$
f (x \oplus y)  = f x \oplus f y
$$

$$
f (s \otimes x) = s \otimes f x
$$

Right away, we've identified several necessities, in addition to those explicitly written above:

1. The $\oplus$ operator must take two arguments of the same type and combine them, returning a result also within the type.

1. Both types $A$ and $B$ _must_ have the $\oplus$ operator defined on them.

1. The $\otimes$ operator must take a scalar as its first argument and some type as its second, returning a result value within that type.

1. Both types $A$ and $B$ _must_ have the $\otimes$ operator defined on them.

We can codify all this in Agda fairly easily:

    data § : Set where
      § : §

    record Additive (A : Set) : Set where
      infixl 6 _⊕_  -- Just matching associativity/priority of `_+_`.
      field
        _⊕_ : A → A → A

    record Scalable (A : Set) : Set where
      infixl 7 _⊛_  -- Just matching associativity/priority of `_*_`.
      field
        _⊛_ : § → A → A

    record LinMap {A B : Set}
                  {{_ : Additive A}} {{_ : Additive B}}
                  {{_ : Scalable A}} {{_ : Scalable B}}
                  : Set where
      field
        f      : A → B
        
        adds   : ∀ (a b : A)
                 ----------------------
               → f (a ⊕ b) ≡ f a ⊕ f b

        scales : ∀ (s : §) (a : A)
                 --------------------
               → f (s ⊛ a) ≡ s ⊛ f a

## Additional Requirements

Okay, let's see if what we've got so far is enough to attack the first isomorphism I'd like to prove: `A ⊸ § ≅ A`, i.e., a linear map from type `A` to scalar is isomorphic to the type `A` itself.
Proving this isomorphism in Agda amounts to constructing the following record:

    a⊸§≃a : ∀ {A : Set} {{_ : Additive A}} {{_ : Scalable A}}
            -------------------------------------------------
          → LinMap {A} {§} ≃ A
    a⊸§≃a = record
      { to   = λ { lm → ? }
      ; from = λ { a  → ? }
      ; from∘to = ?
      ; to∘from = ?
      }

Now, how to implement `to` and `from`?

If we required that `Additive` provide a _left identity_ for `⊕` then it would be enough to require that `A` be able to produce an iterable set of basis vectors.
In that case, `to` could be implemented, via the following:

    to = λ lm → foldl (λ acc v → acc ⊕ (lm.f v) ⊛ v) id-⊕ vs

Implementing `from` is fairly simple, but does require that `A` have an inner product.
In that case, we just build a `LinMap` record where `f` takes the dot product of its
input w/ `a`.

## First Proof Attempt

Let's try adding the extra necessities identified above and attacking the proof.
I'll note any additional properties, record fields, etc. needed to complete the proof, via Agda comments, for subsequent discussion.

```agda
module simple_essence where

open import Data.Float
open import Data.List
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
-- ToDo: Replace w/ equivalent from standard library:
open import plfa_local.part1.Isomorphism

postulate
  -- This one seems completely safe. Why isn't it in the standard library?
  id+ : {x : Float} → 0.0 + x ≡ x

data § : Set where
  S : Float → §

record Additive (A : Set) : Set where
  infixl 6 _⊕_  -- Just matching associativity/priority of `_+_`.
  field
    id⊕  : A
    _⊕_  : A → A → A
    id-⊕ : (a : A)
           ----------
         → id⊕ ⊕ a ≡ a
    -- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
open Additive {{ ... }}
instance
  AdditiveScalar : Additive §
  AdditiveScalar = record
    { id⊕  = S 0.0
    ; _⊕_  = λ {(S x) (S y) → S (x + y)}
    ; id-⊕ = λ { (S x) → begin
                           S (0.0 + x)
                         ≡⟨ cong S id+ ⟩
                           S x
                         ∎
               }
    }

record Scalable (A : Set) : Set where
  infixl 7 _⊛_  -- Just matching associativity/priority of `_*_`.
  field
    _⊛_ : § → A → A
open Scalable {{ ... }}
instance
  ScalableScalar : Scalable §
  ScalableScalar = record
    { _⊛_ = λ {(S x) (S y) → S (x * y)}
    }

record LinMap (A B : Set)
              {{_ : Additive A}} {{_ : Additive B}}
              {{_ : Scalable A}} {{_ : Scalable B}}
              : Set where
  field
    f      : A → B
    
    adds   : ∀ (a b : A)
             ----------------------
           → f (a ⊕ b) ≡ f a ⊕ f b

    scales : ∀ (s : §) (a : A)
             --------------------
           → f (s ⊛ a) ≡ s ⊛ f a
open LinMap {{ ... }}

record VectorSpace (A : Set)
                   {{_ : Additive A}} {{_ : Scalable A}}
                   : Set where
  field
    -- Seems like I should have to define some properties around this:
    basisSet    : List A
    _·_         : A → A → §
    -- Added while solving the isomorphism below.
    ·-distrib-⊕ : ∀ {a b c : A}
                  -------------------------------
                → a · (b ⊕ c) ≡ (a · b) ⊕ (a · c)
    ·-comm-⊛    : ∀ {s : §} {a b : A}
                  -------------------------
                → a · (s ⊛ b) ≡ s ⊛ (a · b)
open VectorSpace {{ ... }}

a⊸§≃a : ∀ {A : Set}
        {{_ : Additive A}} {{_ : Scalable A}}
        {{_ : VectorSpace A}}
        -------------------------------------
      → LinMap A § ≃ A
a⊸§≃a = record
  { to   = λ { lm → foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet }
  ; from = λ { a  → record
                      { f      = λ {x → a · x}
                      ; adds   = λ { v₁ v₂ →
                                       begin
                                          a · (v₁ ⊕ v₂)
                                        ≡⟨ ·-distrib-⊕ ⟩
                                          (a · v₁) ⊕ (a · v₂)
                                        ∎
                                   }
                      ; scales = λ { s b →
                                       begin
                                          a · (s ⊛ b)
                                        ≡⟨ ·-comm-⊛ ⟩
                                          s ⊛ (a · b)
                                        ∎
                                   }
                      }
             }
  ; from∘to =
      λ {lm → let a = foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet
              in  begin
                    record { f      = λ {x → a · x}
                           ; adds   = {! λ {a₁ a₂ → begin
                                                    a · (a₁ ⊕ a₂)
                                                  ≡⟨ ·-distrib-⊕ ⟩  -- {a} {a₁} {a₂} ⟩
                                                    (a · a₁) ⊕ (a · a₂)
                                                  ∎} !}
                           ; scales = {!!}
                           }
                  ≡⟨ {!!} ⟩
                    {!!}
                  ≡⟨ {!!} ⟩
                    {!!}
                  ≡⟨ {!!} ⟩
                    {!!}
                  ≡⟨ {!!} ⟩
                    lm
                  ∎ }
  ; to∘from = {!!}
  }

```

## Agda Imports

Here I define my Agda module and import what it needs from the standard library.

```agda
-- module simple_essence where

-- open import Agda.Primitive
-- open import Data.Bool

```

## Types

In the following subsections I define the types used in my proofs, below.

### Real Proxy and Necessary Postulates

Here I define `Float` as my proxy for real numbers and provide some basic postulates, which are required for my subsequent proofs, but not strictly true for type `Float`.

**ToDo**: Eliminate this, as per Conal's advice, and predicate everything on `Semiring`, instead.

```agda
-- ℜ = Float

-- -- These aren't strictly true for machine types approximating real
-- -- (i.e. - `Float`, etc.), but that's okay for our "demo" purposes here.
-- postulate
--   distrib  : {m a b : ℜ} → m * (a + b) ≡ (m * a) + (m * b)
--   assoc-*  : {a b c : ℜ} → (a * b) * c ≡ a * (b * c)
--   commut-* : {a b   : ℜ} → a * b       ≡ b * a
--   assoc-+  : {a b c : ℜ} → (a + b) + c ≡ a + (b + c)
--   commut-+ : {a b   : ℜ} → a + b       ≡ b + a

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

```

#### Scalar Addition

Scalar addition is defined by requiring that a sum of scalars is a scalar of the sum.

```agda
-- infixl 6 _+§_  -- Just using the associativity/priority of ordinary addition.
-- _+§_ : Scalar → Scalar → Scalar
-- (§ x) +§ (§ y) = § (x + y)

```

We can show that it is both *associative* and *commutative*, thanks to the associativity and commutativity of the underlying real field upon which it depends.

```agda
-- assoc-+§ : (x y z : Scalar)
--            -----------------------------
--          → (x +§ y) +§ z ≡ x +§ (y +§ z)
-- assoc-+§ (§ x) (§ y) (§ z) =
--   begin
--     ((§ x) +§ (§ y)) +§ (§ z)
--   ≡⟨⟩
--     (§ (x + y)) +§ (§ z)
--   ≡⟨⟩
--     § ((x + y) + z)
--   ≡⟨ cong § (assoc-+ {x}) ⟩
--     § (x + (y + z))
--   ≡⟨⟩
--     (§ x) +§ (§ (y + z))
--   ≡⟨⟩
--     (§ x) +§ ((§ y) +§ (§ z))
--   ∎

-- commut-+§ : (x y : Scalar)
--             ---------------
--           → x +§ y ≡ y +§ x
-- commut-+§ (§ x) (§ y) =
--   begin
--     (§ x) +§ (§ y)
--   ≡⟨⟩
--     § (x + y)
--   ≡⟨ cong § (commut-+ {x}) ⟩
--     § (y + x)
--   ≡⟨⟩
--     (§ y) +§ (§ x)
--   ∎

```

#### Scalar Multiplication by Real

Again, we simply require the operator to be an endofunctor.
And we can show distributivity.

```agda
-- infixl 7 _*§_
-- _*§_ : ℜ → Scalar → Scalar
-- x *§ (§ y) = § (x * y)

-- distrib-*§ : (s : ℜ) → (x y : Scalar)
--              --------------------------------
--            → s *§ (x +§ y) ≡ s *§ x +§ s *§ y
-- distrib-*§ s (§ x) (§ y) =
--   begin
--     s *§ (§ x +§ § y)
--   ≡⟨⟩
--     s *§ § (x + y)
--   ≡⟨⟩
--     § (s * (x + y))
--   ≡⟨ cong § (distrib {s}) ⟩
--     § ((s * x) + (s * y))
--   ≡⟨⟩
--     § (s * x) +§ § (s * y)
--   ≡⟨⟩
--     s *§ (§ x) +§ s *§ (§ y)
--   ∎

```

### Pairs

I use *nonuniform* pairs, to allow for maximum flexibility in assembling composite types.
I also provide the "cross" operator from Conal's paper, in both unary and binary form.

```agda
-- infixl 5 _,_
-- data Pair (A B : Set) : Set where
--   _,_ : (x : A) → (y : B) → Pair A B

-- _Χ_ : {A B C D : Set} → (A → C) → (B → D) → Pair A B → Pair C D
-- f Χ g = λ {(x , y) → ((f x) , (g y))}

-- _Χ₂_ : {A B C D E F : Set} → (A → C → E) → (B → D → F) → Pair A B → Pair C D → Pair E F
-- f Χ₂ g = λ {(x , y) (w , z) → ((f x w) , (g y z))}

```

## Type Classes

Here I define some classes of types with useful common properties.

### Additive Types

The type class `Additive` just requires an *associative* binary joining operator, which accepts two arguments within the type and produces a result also within the type.
In order to be a member of this class, _all_ elements of the candidate type must be suitable as inputs (in either position) to this joining operator.

```agda

```

All of our previously defined types, except `Term`,  have `Additive` instances:

```agda
-- instance
--   RealAdditive : Additive ℜ
--   RealAdditive = record
--     { _⊕_     = _+_
--     ; assoc-⊕ = λ {x y z → assoc-+ {x} {y} {z}}
--     }

--   ScalarAdditive : Additive Scalar
--   ScalarAdditive = record
--     { _⊕_ = _+§_
--     ; assoc-⊕ = λ {x y z → assoc-+§ x y z}
--     }

--   -- ToDo: Review paper, to determine proper spec. for this implementation.
--   PairAdditive : {A B : Set} {{_ : Additive A}} {{_ : Additive B}}
--                → Additive (Pair A B)
--   PairAdditive = record
--     { _⊕_ = (_⊕_ Χ₂ _⊕_)
--     ; assoc-⊕ =
--         λ { (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) →
--               begin
--                 (x₁ ⊕ y₁ ⊕ z₁   , x₂ ⊕ y₂ ⊕ z₂)
--               ≡⟨ cong (_, x₂ ⊕ y₂ ⊕ z₂) (assoc-⊕ x₁ y₁ z₁) ⟩
--                 (x₁ ⊕ (y₁ ⊕ z₁) , x₂ ⊕ y₂ ⊕ z₂)
--               ≡⟨ cong (x₁ ⊕ (y₁ ⊕ z₁) ,_) (assoc-⊕ x₂ y₂ z₂) ⟩
--                 (x₁ ⊕ (y₁ ⊕ z₁) , x₂ ⊕ (y₂ ⊕ z₂))
--               ∎
--           }
--     }

--   -- TermAdditive : Additive Term
--   -- TermAdditive = record
--   --   { _⊕_ =
--   --     λ { (σ x) (σ y)         → σ (x + y)
--   --       ; (σ x) (y₁ , y₂)     → σ x ⊕ y₁ , σ x ⊕ y₂
--   --       ; (x₁ , x₂) (σ y)     → {!!}
--   --       ; (x₁ , x₂) (y₁ , y₂) → {!!}}
--   --   ; assoc-⊕ = {!!}
--   --   }

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
```

Again, all of our previously defined types, except `Term`, have instances:

```agda
-- instance
--   RealScalable : Scalable ℜ
--   RealScalable = record { _⊛_ = _*_ }

--   ScalarScalable : Scalable Scalar
--   ScalarScalable = record { _⊛_ = _*§_ }
  
--   -- ToDo: Review paper, to determine proper spec. for this implementation.
--   PairScalable : {A B : Set} {{_ : Scalable A}} {{_ : Scalable B}} → Scalable (Pair A B)
--   PairScalable = record { _⊛_ = λ m → (m ⊛_) Χ (m ⊛_) }

```

### Linear Maps

This class captures the meaning of _linearity_.
The class considers a function to be linear if it (as Conal notes in his paper) distributes over addition and scaling.

```agda

```

#### Linear Scalar Map

Here is a linear map between scalars.
It is simply a line in the xy-plane translating x-coordinate inputs to y-coordinate outputs.
Since it must pass through the origin, in order to be linear, it is defined by a single quantity: its *slope*, which I refer to in the code as `m`, following what I learned in high school trigonometry class.

```agda
-- scalar-map : ℜ → LinMap {ℜ} {ℜ}
-- scalar-map m = record
--   { f      = m *_
--   ; adds   = λ a b → distrib {m} {a} {b}
--   ; scales =
--       λ { s a → begin
--                   m * (s * a)
--                 ≡⟨ sym (assoc-* {m}) ⟩
--                   (m * s) * a
--                 ≡⟨ cong (_* a) (commut-* {m} {s}) ⟩
--                   (s * m) * a
--                 ≡⟨ assoc-* {s} ⟩
--                   s * (m * a)
--                 ∎
--         }
--   }

-- -- To accommodate `_≃_`, which only accepts arguments of type `Set`.
-- record ScalarMap : Set where
--   field
--     m : ℜ
--   map : LinMap {ℜ} {ℜ}
--   map = scalar-map m

```

#### Linear Map from Pair of Scalars to Scalar

**Note:** I've arbitrarily chosen to _sum_ the partial products, in order to form the final result.
I might have, instead, taken their product.
What justifies this choice?

```agda
-- pair-map : Pair ℜ ℜ → LinMap {Pair ℜ ℜ} {ℜ}
-- pair-map (m₁ , m₂) = record
--   { f = λ { (x , y) → (m₁ * x) + (m₂ * y) }
--   ; adds = λ { (x , y) (x₁ , y₁) →
--                  begin
--                    (m₁ * (x + x₁)) + (m₂ * (y + y₁))
--                  ≡⟨ cong (_+ (m₂ * (y + y₁))) (distrib {m₁} {x} {x₁}) ⟩
--                    ((m₁ * x) + (m₁ * x₁)) + (m₂ * (y + y₁))
--                  ≡⟨ cong (((m₁ * x) + (m₁ * x₁)) +_) (distrib {m₂} {y} {y₁}) ⟩
--                    ((m₁ * x) + (m₁ * x₁)) + ((m₂ * y) + (m₂ * y₁))
--                  ≡⟨ sym (assoc-+ {(m₁ * x) + (m₁ * x₁)} {(m₂ * y)} {(m₂ * y₁)}) ⟩
--                    (((m₁ * x) + (m₁ * x₁)) + (m₂ * y)) + (m₂ * y₁)
--                  ≡⟨ cong (_+ (m₂ * y₁)) (assoc-+ {(m₁ * x)} {(m₁ * x₁)} {(m₂ * y)}) ⟩
--                    ((m₁ * x) + ((m₁ * x₁) + (m₂ * y))) + (m₂ * y₁)
--                  ≡⟨ sym (sym (assoc-+ {m₁ * x} {(m₁ * x₁) + (m₂ * y)} {m₂ * y₁})) ⟩
--                    (m₁ * x) + (((m₁ * x₁) + (m₂ * y)) + (m₂ * y₁))
--                  ≡⟨ cong ((m₁ * x) +_) (cong (_+ (m₂ * y₁)) (commut-+ {m₁ * x₁} {m₂ * y})) ⟩
--                    (m₁ * x) + (((m₂ * y) + (m₁ * x₁)) + (m₂ * y₁))
--                  ≡⟨ cong ((m₁ * x) +_) (sym (sym (assoc-+ {m₂ * y} {m₁ * x₁} {m₂ * y₁}))) ⟩
--                    (m₁ * x) + ((m₂ * y) + ((m₁ * x₁) + (m₂ * y₁)))
--                  ≡⟨ sym (assoc-+ {m₁ * x} {m₂ * y} {(m₁ * x₁) + (m₂ * y₁)}) ⟩
--                    ((m₁ * x) + (m₂ * y)) + ((m₁ * x₁) + (m₂ * y₁))
--                  ∎
--              }
--   ; scales = λ { s (x , y) →
--                    begin
--                      (m₁ * (s * x)) + (m₂ * (s * y))
--                    ≡⟨ cong (_+ (m₂ * (s * y))) (sym (assoc-* {m₁} {s} {x})) ⟩
--                      ((m₁ * s) * x) + (m₂ * (s * y))
--                    ≡⟨ cong (_+ (m₂ * (s * y))) (cong (_* x) (commut-* {m₁} {s})) ⟩
--                      ((s * m₁) * x) + (m₂ * (s * y))
--                    ≡⟨ cong (_+ (m₂ * (s * y))) (assoc-* {s} {m₁} {x}) ⟩
--                      (s * (m₁ * x)) + (m₂ * (s * y))
--                    ≡⟨ cong ((s * (m₁ * x)) +_) (sym (assoc-* {m₂} {s} {y})) ⟩
--                      (s * (m₁ * x)) + ((m₂ * s) * y)
--                    ≡⟨ cong ((s * (m₁ * x)) +_) (cong (_* y) (commut-* {m₂} {s})) ⟩
--                      (s * (m₁ * x)) + ((s * m₂) * y)
--                    ≡⟨ cong ((s * (m₁ * x)) +_) (sym (sym (assoc-* {s} {m₂} {y}))) ⟩
--                      (s * (m₁ * x)) + (s * (m₂ * y))
--                    ≡⟨ sym (distrib {s} {m₁ * x} {m₂ * y}) ⟩
--                      s * ((m₁ * x) + (m₂ * y))
--                    ∎
--                }
--   }

-- record PairMap : Set where
--   field
--     ms : Pair ℜ ℜ
--   map : LinMap {Pair ℜ ℜ} {ℜ}
--   map = pair-map ms

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

```
