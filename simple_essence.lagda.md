---
format: 'markdown+latex'
title: 'Agda Doodlings Involving Linearity & Vector Spaces'
description: Agda proofs of some isomorphisms revealed by Conal in his paper.
author: 'David Banas <capn.freako@gmail.com>'
date: 2022-04-02
copy: Copyright (c) 2022 David Banas; all rights reserved World wide.
...

{% include mathjax.html %}

<link rel="stylesheet" type="text/css" href="Agda.css">

In this [literate Agda](https://agda.readthedocs.io/en/v2.6.2.1/tools/literate-programming.html#literate-markdown) file I'm exploring some of the ideas written about by Conal Elliott in his paper: _The Simple Essence of Automatic Differentiation_.
In particular, I'm attempting to prove, using Agda, some of the isomorphisms that Conal reveals in that paper.

## Introduction

In (re)reading Conal's paper, I noticed something that I thought was a typo:

> The internal representation of $$Cont^{s}_{(⊸)} \, a \, b$$ is $$(b ⊸ s) → (a ⊸ s)$$, which is isomorphic to $$b → a$$.

I thought for sure Conal meant to say:

> ... isomorphic to $$a → b$$.

since the continuation must "know" how to get from `a` to `b`, in order to offer the type signature it does.
(Can this be proven in Agda, perhaps by using a proof-by-contradiction approach?)

But, when I discussed this with Conal, he drew my attention to the paragraph immediately above, in which he points out:

> In particular, every linear map in $$A ⊸ s$$ has the form `dot u` for some `u :: A`,

And that, therefore, since $$a ⊸ s$$ is isomorphic to $$a$$,  $$(b ⊸ s) → (a ⊸ s)$$ is indeed isomorphic to $$b → a$$.

Well, that's very interesting, because now we've got something (the _continuation_) that is isomorphic to both $$a → b$$ and $$b → a$$.
And, because the isomorphism relation is _transitive_, that means: $$a → b ≅ b → a$$!
Of course, this only holds in the special case where both types $$a$$ and $$b$$ have linear maps to the underlying scalar field.
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

1. The $$\oplus$$ operator must take two arguments of the same type and combine them, returning a result also within the type.

1. Both types $$A$$ and $$B$$ _must_ have the $$\oplus$$ operator defined on them.

1. The $$\otimes$$ operator must take a scalar as its first argument and some type as its second, returning a result value within that type.

1. Both types $$A$$ and $$B$$ _must_ have the $$\otimes$$ operator defined on them.

We can codify all this in Agda fairly easily:

    {% highlight haskell linenos %}
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
                  ⦃_ : Additive A⦄ ⦃_ : Additive B⦄
                  ⦃_ : Scalable A⦄ ⦃_ : Scalable B⦄
                  : Set where
      field
        f      : A → B

        adds   : ∀ (a b : A)
                 ----------------------
               → f (a ⊕ b) ≡ f a ⊕ f b

        scales : ∀ (s : §) (a : A)
                 --------------------
               → f (s ⊛ a) ≡ s ⊛ f a
    {% endhighlight %}

## Additional Requirements

Okay, let's see if what we've got so far is enough to attack the first isomorphism I'd like to prove: `A ⊸ § ≅ A`, i.e., a linear map from type `A` to scalar is isomorphic to the type `A` itself.
Proving this isomorphism in Agda amounts to constructing the following record:

    {% highlight haskell linenos %}
    a⊸§≃a : ∀ {A : Set} ⦃_ : Additive A⦄ ⦃_ : Scalable A⦄
             --------------------------------------------
           → LinMap {A} {§} ≃ A
    a⊸§≃a = record
      { to   = λ { lm → ? }
      ; from = λ { a  → ? }
      ; from∘to = ?
      ; to∘from = ?
      }
    {% endhighlight %}

Now, how to implement `to` and `from`?

If we required that `Additive` provide a _left identity_ for `⊕` then it would be enough to require that `A` be able to produce an iterable set of basis vectors.
In that case, `to` could be implemented, via the following:

{% highlight haskell linenos %}
    to = λ lm → foldl (λ acc v → acc ⊕ (lm.f v) ⊛ v) id-⊕ vs
{% endhighlight %}

Implementing `from` is fairly simple, but does require that `A` have an inner product.
In that case, we just build a `LinMap` record where `f` takes the dot product of its
input w/ `a`.

**Note:** My hunch is that I'm going to have to define some property of type `A` that relates the "inner product" to its "basis vectors", in order to tie all this together, but it's unclear to me what that property is, or needs to be.

## First Proof Attempt

Let's try adding the extra necessities identified above and attacking the proof.
I'll note any additional properties, record fields, etc. needed to complete the proof, via Agda comments, for subsequent discussion.

### Imports, Variables, and Postulates

Here, we import everything we'll need later and define our module-wide variables and postulates.

```agda
module simple_essence where

open import Agda.Builtin.Sigma
open import Algebra                            using (IsRing; IsNearSemiring)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.List
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Function     using (_↔_; mk↔; id; const)
open import Level        using (Level; _⊔_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; _≢_)
open Eq.≡-Reasoning                   using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

variable
  ℓ₁ ℓ₂ ℓ₃ : Level
  
postulate
  extensionality : Extensionality ℓ₁ ℓ₂

```

### Type Classes

Here, we define the abstract type classes we'll be using in our proofs.
We use a slight variation on the approach taken in the standard library "bundles", because it yields cleaner, more succinct, abstract code capable of _automatic instance selection_.

**Note:** We've removed our previously defined custom typeclass: `Additive`, in favor of `Ring` defined in the Agda standard library.
We've kept `Scalable`, for now, in order to get some incremental progress working and checked in before attempting to use `Module` and friends.

```agda
record Scalable (T : Set ℓ₁) (A : Set ℓ₁) : Set (Level.suc ℓ₁) where
  infix 7 _·_
  field
    _·_ : A → T → T
open Scalable ⦃ ... ⦄ public

record Ring (A : Set ℓ₁) : Set (Level.suc ℓ₁) where
  infixl 6 _+_
  infixl 7 _*_
  infix  8 -_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    -_  : A → A
    𝟘   : A
    𝟙   : A
    ⦃ isRing ⦄ : IsRing _≡_ _+_ _*_ -_ 𝟘 𝟙
  open IsRing isRing public
  instance
    scalableRing : Scalable A A
    scalableRing = record
      { _·_ = _*_
      }
  open Scalable scalableRing
open Ring ⦃ ... ⦄ public
    
```

### Linear Maps

Here, we capture our intended meaning of _linearity_.

We take the vector-centric definition offered by Conal in his paper:

> A linear map is one that distributes over _vector_ addition and _scalar_ multiplication.

```agda
record LinMap (A : Set ℓ₁) (B : Set ℓ₁) {§ : Set ℓ₁}
              ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄
              ⦃ _ : Scalable A § ⦄   ⦃ _ : Scalable B § ⦄
              : Set ℓ₁ where
  constructor mkLM
  field
    f      : A → B

    adds   : ∀ {a b : A}
             ---------------------
          → f (a + b) ≡ f a + f b

    scales : ∀ {s : §} {a : A}
             -------------------
          → f (s · a) ≡ s · f a

open LinMap ⦃ ... ⦄ public

-- As per Conal's advice:
-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence
postulate
  ⊸≡ : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
       ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄
       ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
       {lm₁ lm₂ : LinMap A B {§}}
    → LinMap.f lm₁ ≡ LinMap.f lm₂
       --------------------------
    → lm₁ ≡ lm₂

```

### Vector Spaces

Here, we define what we mean by a _vector space_.

In its most general sense, a "vector space" provides a function that takes some _index_ type and uses it to map from some _container_ type to a single value of the _carrier_ type.

We add a few extras, useful when doing _linear algebra_:

Vector Addition
:   We can "add" two vectors, producing a third.

Scalar Multiplication
:   We can "scale" a vector by an element of the carrier type, producing another vector.

Inner Product
:   We can combine two vectors, producing a single value of the carrier type.

**Note:** The remaining definitions in the code below were the result of attempting to solve the first isomorphism.

**Note:** We use `Ring`, as opposed to a `SemiRing`, because that gives us _subtraction_, which allows us to prove _injectivity_ of linear maps, which in turn allows us to replace the `x·z≡y·z→x≡y` _postulate_ with an equivalent _proof_.

```agda
record VectorSpace
  (T : Set ℓ₁) (A : Set ℓ₁)
  ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄ ⦃ _ : Scalable T A ⦄
  : Set (Level.suc ℓ₁) where
  infix  7 _⊙_
  field
    I     : Set ℓ₁
    index : I → T → A
    basisSet    : List T
    _⊙_         : T → T → A
    -- Added while solving the isomorphism below.
    ⊙-distrib-+ : ∀ {a b c : T}
                  -------------------------------
               → a ⊙ (b + c) ≡ (a ⊙ b) + (a ⊙ c)
    ⊙-comm-·    : ∀ {s : A} {a b : T}
                  -------------------------
               → a ⊙ (s · b) ≡ s · (a ⊙ b)
    orthonormal : ∀ {f : T → A}
               → {x : T}
                  ------------------------------------
               → ( foldl (λ acc v → acc + (f v) · v)
                          𝟘 basisSet
                  ) ⊙ x ≡ f x
open VectorSpace ⦃ ... ⦄ public

```

### Isomorphism 1: `(A ⊸ s) ↔ A`

Here, I prove that a linear map from some "vector" type `T` to a scalar of its _carrier_ type `A` is isomorphic to `T`.

```agda
a⊸§→a : {T : Set ℓ₁} {A : Set ℓ₁}
         ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
         ⦃ _ : Scalable T A ⦄
         ⦃ _ : VectorSpace T A ⦄
         ------------------------------
      → LinMap T A {A} → T
a⊸§→a = λ { lm → foldl (λ acc v →
                     acc + (LinMap.f lm v) · v) 𝟘 basisSet }

a⊸§←a : {T : Set ℓ₁} {A : Set ℓ₁}
         ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
         ⦃ _ : Scalable T A ⦄
         ⦃ _ : VectorSpace T A ⦄
         --------------------------------------
      → T → LinMap T A {A}
a⊸§←a = λ { a → mkLM (a ⊙_) ⊙-distrib-+ ⊙-comm-· }

-- Danger, Will Robinson!
postulate
  x·z≡y·z→x≡y : {T : Set ℓ₁} {A : Set ℓ₁}
                 ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
                 ⦃ _ : Scalable T A ⦄ ⦃ _ : VectorSpace T A ⦄
                 {x y : T}
              → (∀ {z : T} → x ⊙ z ≡ y ⊙ z)
                 ---------------------------------------------
              → x ≡ y
-- ToDo: Try replacing postulate above w/ definition below.
--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)
-- x·z≡y·z→x≡y x·z≡y·z = {!!}

a⊸§↔a : {T : Set ℓ₁} {A : Set ℓ₁}
         ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
         ⦃ _ : Scalable T A ⦄ ⦃ _ : VectorSpace T A ⦄
         ---------------------------------------------
      → (LinMap T A) ↔ T
a⊸§↔a =
  mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}
      ( (λ {x → begin
                  a⊸§→a (a⊸§←a x)
                ≡⟨⟩
                  a⊸§→a (mkLM (x ⊙_) ⊙-distrib-+ ⊙-comm-·)
                ≡⟨⟩
                  foldl (λ acc v → acc + (x ⊙ v) · v) 𝟘 basisSet
                ≡⟨ x·z≡y·z→x≡y orthonormal ⟩
                  x
                ∎})
      , λ {lm → begin
                    a⊸§←a (a⊸§→a lm)
                  ≡⟨⟩
                    a⊸§←a (foldl (λ acc v →
                                     acc + (LinMap.f lm v) · v) 𝟘 basisSet)
                  ≡⟨⟩
                    mkLM ( foldl ( λ acc v →
                                     acc + (LinMap.f lm v) · v
                                 ) 𝟘 basisSet
                           ⊙_
                         ) ⊙-distrib-+ ⊙-comm-·
                  ≡⟨ ⊸≡ ( extensionality
                            ( λ x → orthonormal {f = LinMap.f lm} {x = x} )
                        )
                   ⟩
                    lm
                  ∎}
      )

```

### Stashed

Stashed coding attempts.

```agda
-- This, done in response to Conal's suggestion of using `Equivalence`, instead of
-- `Equality`, compiles fine but seems too easy and too weak.
-- There's no guarantee of returning back where we started after a double pass, for instance.
-- I think that I didn't fully grok the hint he was giving me.
--
-- a⊸§⇔a : {A : Set a}
--         ⦃_ : Additive A⦄ ⦃_ : Scalable A⦄
--         ⦃_ : VectorSpace A⦄
--         -------------------------------------
--       → (LinMap A §) ⇔ A
-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a

-- -- f(0) = 0
-- zero-lin : {A B : Set a}
--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄
--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄
--           ⦃ _ : LinMap A B ⦄

-- -- Injectivity of linear function
-- inj-lin : {A B : Set a} {x y : A}
--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄
--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄
--           ⦃ _ : LinMap A B ⦄
--        → LinMap.f _ x ≡ LinMap.f _ y
--           ---------------------------
--        → x ≡ y
-- inj-lin {x = x} {y = y} fx≡fy =
--   let f = LinMap.f _
--    in begin
--         x
--       ≡⟨⟩
--         f (x - y)
--       ≡⟨ LinMap.adds _ ⟩
--         f x - f y
--       ≡⟨ sub-≡ fx≡fy ⟩
--         0
--       ≡⟨⟩
--         y
--       ∎
      
-- cong-app′ : ∀ {A : Set a} {B : Set b} {f : A → B} {x y : A}
--          → f x ≡ f y
--             ---------
--          → x ≡ y
-- cong-app′ fx≡fy = {!contraposition!}
         
-- x·z≡y·z→x≡y : {A : Set a}
--                ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄
--                ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄
--                {x y : A}
--             → (∀ {z : A} → x · z ≡ y · z)
--                ------------------------------------------------------------
--             → x ≡ y
-- x·z≡y·z→x≡y {x = x} {y = y} g =
--   let f = LinMap.f _
--       z = foldl (λ acc v → acc ⊕ f v ⊛ v) id⊕ basisSet
--       x·z≡y·z = g {z}
--    in cong-app refl {!!}
--    -- in begin
--    --      -- ?
--    --      x·z≡y·z
--    --    -- ≡⟨ ? ⟩
--    --    --   x · z ≡ y · z
--    --    ≡⟨ ? ⟩
--    --    -- ≡⟨ cong (_≡ y · z) comm-· ⟩
--    --      z · x ≡ y · z
--    --    ≡⟨ ? ⟩
--    --    -- ≡⟨ cong (z · x ≡_) comm-· ⟩
--    --      z · x ≡ z · y
--    --    ≡⟨ ? ⟩
--    --    -- ≡⟨ cong (_≡ z · y) (orthonormal) ⟩
--    --      f x ≡ z · y
--    --    ≡⟨ ? ⟩
--    --    -- ≡⟨ cong (f x ≡_) (orthonormal) ⟩
--    --      f x ≡ f y
--    --    ≡⟨ ? ⟩
--    --    -- ≡⟨ cong-app ⟩
--    --      x ≡ y
--    --    ∎

-- -- So, how was Agsy able to jump over all of that?
-- -- My usual experience w/ Agsy is that when I ask it to solve anything
-- -- non-trivial by itself it always complains, "Sorry, I don't support
-- -- literals, yet.", which I've never understood.

-- a⊸§↔a : {A : Set a}
--          ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄
--          ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄
--          -----------------------------------------
--       → (LinMap A §) ↔ A
-- a⊸§↔a {A} =
--   mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}
--       ( (λ {x → begin
--                   a⊸§→a (a⊸§←a x)
--                 ≡⟨⟩
--                   a⊸§→a (mkLM (x ·_) ·-distrib-⊕ ·-comm-⊛)
--                 ≡⟨⟩
--                   foldl (λ acc v → acc ⊕ (x · v) ⊛ v) id⊕ basisSet
--                 ≡⟨ x·z≡y·z→x≡y (orthonormal {f = (x ·_)}) ⟩
--                   x
--                 ∎})
--       , λ {lm → begin
--                   a⊸§←a (a⊸§→a lm)
--                 ≡⟨⟩
--                   a⊸§←a (foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)
--                 ≡⟨⟩
--                   mkLM ((foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)·_)
--                        ·-distrib-⊕ ·-comm-⊛
--                 ≡⟨ ⊸≡ ( extensionality
--                           ( λ x → orthonormal {f = LinMap.f lm} {x = x} )
--                       )
--                  ⟩
--                   lm
--                 ∎}
--       )


```
