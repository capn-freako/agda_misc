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

**Note:** My hunch is that I'm going to have to define some property of type `A` that relates the "inner product" to its "basis vectors", in order to tie all this together, but it's unclear to me what that property is, or needs to be.

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
  constructor mkLM
  field
    f      : A → B
    
    adds   : ∀ {a b : A}
             ---------------------
           → f (a ⊕ b) ≡ f a ⊕ f b

    scales : ∀ {s : §} {a : A}
             -------------------
           → f (s ⊛ a) ≡ s ⊛ f a
open LinMap {{ ... }}

record VectorSpace (A : Set)
                   {{_ : Additive A}} {{_ : Scalable A}}
                   : Set where
  field
    -- As noted above, seems like I should have to define some properties relating these two.
    basisSet    : List A
    _·_         : A → A → §
    -- Added while solving the isomorphism below.
    ·-distrib-⊕ : ∀ {a b c : A}
                  -------------------------------
                → a · (b ⊕ c) ≡ (a · b) ⊕ (a · c)
    ·-comm-⊛    : ∀ {s : §} {a b : A}
                  -------------------------
                → a · (s ⊛ b) ≡ s ⊛ (a · b)
    -- Aha! Here's that property relating `basisSet` and `(_·_)` I was hunching on.
    -- Needed to complete the definition of `from∘to` below.
    orthonormal : ∀ {f : A → §} {x : A}
                  ----------------------------------------------------------
                → (foldl (λ acc v → acc ⊕ (f v) ⊛ v) id⊕ basisSet) · x ≡ f x
    -- orthonormal : ∀ {f : A → §}
    --               ----------------------------------------------------------
    --             → (foldl (λ acc v → acc ⊕ (f v) ⊛ v) id⊕ basisSet) ·_ ≡ f
open VectorSpace {{ ... }}

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y z u v w}
      → x ≡ u → y ≡ v → z ≡ w → f x y z ≡ f u v w
cong₃ f refl refl refl = refl

a⊸§≃a : ∀ {A : Set}
        {{_ : Additive A}} {{_ : Scalable A}}
        {{_ : VectorSpace A}}
        -------------------------------------
      → LinMap A § ≃ A
a⊸§≃a =
  record
       { to   = λ { lm → foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet }
       ; from = λ { a  → mkLM (a ·_) ·-distrib-⊕ ·-comm-⊛ }
       ; from∘to =
           λ {lm → let f′ = LinMap.f lm
                       a  = foldl (λ acc v → acc ⊕ (f′ v) ⊛ v) id⊕ basisSet
                   in begin
                        mkLM (a ·_) ·-distrib-⊕ ·-comm-⊛
                      ≡⟨ {!cong₃ mkLM ? ? ?!} ⟩
                        mkLM f′ (LinMap.adds lm) (LinMap.scales lm)
                      ≡⟨⟩
                        lm
                      ∎ }
       ; to∘from = {!!}
       }

```

