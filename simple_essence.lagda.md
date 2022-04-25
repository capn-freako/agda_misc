---
format: 'markdown+latex'
title: 'Agda Doodlings Involving Linearity & Vector Spaces'
description: Agda proofs of some isomorphisms revealed by Conal in his paper.
author: 'David Banas <capn.freako@gmail.com>'
date: 2022-04-02
copy: Copyright (c) 2022 David Banas; all rights reserved World wide.
toc: true
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
  extensionality  : Extensionality ℓ₁ ℓ₂
  excluded-middle : ∀ {A : Set ℓ₁} → ¬ (¬ A) ≡ A
  ≡-involutive    : ∀ {A : Set ℓ₁} → {x y : A} → ¬ (x ≢ y) → x ≡ y

```

### Type Classes

Here, we define the abstract type classes we'll be using in our proofs.
We use a slight variation on the approach taken in the standard library "bundles", because it yields cleaner, more succinct, abstract code capable of _automatic instance selection_.

**Note:** We've removed our previously defined custom typeclass: `Additive`, in favor of `Ring` defined in the Agda standard library.
We've kept `Scalable`, for now, in order to get some incremental progress working and checked in before attempting to use `Module` and friends.

```agda
record Ring (A : Set ℓ₁) : Set (Level.suc ℓ₁) where
  infixl 6 _+_
  infixl 7 _*_
  infix  8 -_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    -_  : A → A
    -‿involutive : {x : A} → - (- x) ≡ x
    𝟘   : A
    𝟙   : A
    ⦃ isRing ⦄ : IsRing _≡_ _+_ _*_ -_ 𝟘 𝟙
  open IsRing isRing public
open Ring ⦃ ... ⦄ public
    
record Scalable (T : Set ℓ₁) (A : Set ℓ₁)
                ⦃ _ : Ring A ⦄ ⦃ _ : Ring T ⦄
                : Set (Level.suc ℓ₁) where
  infix 7 _·_
  field
    _·_ : A → T → T
    an𝟘ˡ : (v : T)
           ---------
        → 𝟘 · v ≡ 𝟘
    an𝟘ʳ : (s : A)
           ---------
        → s · 𝟘 ≡ 𝟘
    id𝟙 : (v : T)
          ---------
       → 𝟙 · v ≡ v
open Scalable ⦃ ... ⦄ public

record ScalableCont (T : Set ℓ₁) (A : Set ℓ₁)
                    ⦃ _ : Ring A ⦄ ⦃ _ : Ring T ⦄ ⦃ _ : Scalable T A ⦄
                    : Set (Level.suc ℓ₁) where
  field
    cont : ∀ (x y : T)
        → Σ[ s ∈ A ] s · x ≡ y
open ScalableCont ⦃ ... ⦄ public

non-zeroˡ : {T A : Set ℓ₁} ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
            ⦃ _ : Scalable T A ⦄ {s : A} {v : T}
         → s · v ≢ 𝟘
            ---------
         → s ≢ 𝟘
non-zeroˡ {s = s} {v = v} s·v≢𝟘 = λ { s≡𝟘 →
  let s·v≡𝟘 : s · v ≡ 𝟘
      s·v≡𝟘 = begin
                s · v
              ≡⟨ cong (_· v) s≡𝟘 ⟩
                𝟘 · v
              ≡⟨ an𝟘ˡ v ⟩
                𝟘
              ∎
   in s·v≢𝟘 s·v≡𝟘
  }

non-zeroʳ : {T A : Set ℓ₁} ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
            ⦃ _ : Scalable T A ⦄ {s : A} {v : T}
         → s · v ≢ 𝟘
            ---------
         → v ≢ 𝟘
non-zeroʳ {s = s} {v = v} s·v≢𝟘 = λ { v≡𝟘 →
  let s·v≡𝟘 : s · v ≡ 𝟘
      s·v≡𝟘 = begin
                s · v
              ≡⟨ cong (s ·_) v≡𝟘 ⟩
                s · 𝟘
              ≡⟨ an𝟘ʳ s ⟩
                𝟘
              ∎
   in s·v≢𝟘 s·v≡𝟘
  }

instance
  scalableRing : {A : Set ℓ₁} ⦃ _ : Ring A ⦄ → Scalable A A
  scalableRing = record
    { _·_  = _*_
    ; an𝟘ˡ = λ {x → zeroˡ x}
    ; an𝟘ʳ = λ {x → zeroʳ x}
    ; id𝟙  = λ {x → *-identityˡ x}
    }

```

### Linear Maps

Here, we capture our intended meaning of _linearity_.

We take the vector-centric definition offered by Conal in his paper:

> A linear map is one that distributes over _vector_ addition and _scalar_ multiplication.

We require our linear maps to be non-trivial (i.e. - `f ≢ const 𝟘`).
If we don't do this here then we have to add an argument of the same type to many of the lemmas and proofs below.
The loss of generality seems rather benign, in this case.

```agda
record LinMap (A : Set ℓ₁) (B : Set ℓ₁) {§ : Set ℓ₁}
              ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
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
    -- nontrivial : Σ[ a ∈ A ] f a ≢ 𝟘

open LinMap ⦃ ... ⦄ public

```

#### Equivalence of Linear Maps

As per a helpful suggestion from Conal, we ignore the `adds` and `scales` fields when testing two linear maps for equivalence, comparing just their functions.
Note that neither could've been constructed w/o `adds` and `scales` fields apropos to its `f` field.

```agda
-- As per Conal's advice:
-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence
postulate
  ⊸≡ : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
       ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
       ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
       {lm₁ lm₂ : LinMap A B {§}}
    → LinMap.f lm₁ ≡ LinMap.f lm₂
       --------------------------
    → lm₁ ≡ lm₂

```

#### Axioms of Linearity

Here we code up some well known axioms of linearity, for use in various lemmas and proofs below.

```agda
-- f(0) ≡ 0, for linear f
f𝟘≡𝟘 : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
       ⦃ ringA : Ring A ⦄ ⦃ ringB : Ring B ⦄ ⦃ ring§ : Ring § ⦄
       ⦃ scalA§ : Scalable A § ⦄ ⦃ scalB§ : Scalable B § ⦄
       ⦃ lmAB : LinMap A B {§} ⦄ {x : A}
       ------------------------------------------
    → f 𝟘 ≡ 𝟘
f𝟘≡𝟘 {x = x} =
  begin
    f 𝟘
  ≡⟨ cong f (Eq.sym (an𝟘ˡ x)) ⟩
    f (𝟘 · x)
  ≡⟨ scales ⟩
    𝟘 · f x
  ≡⟨ an𝟘ˡ (f x) ⟩
    𝟘
  ∎

x≡𝟘→fx≡𝟘 : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
            ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
            ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
            ⦃ _ : LinMap A B {§} ⦄ {x : A}
         → x ≡ 𝟘
            -------
         → f x ≡ 𝟘
x≡𝟘→fx≡𝟘 {x = x} x≡𝟘 = begin
                  f x
                ≡⟨ cong f x≡𝟘 ⟩
                  f 𝟘
                ≡⟨ f𝟘≡𝟘 {x = x} ⟩
                  𝟘
                ∎
           
fx≢𝟘→x≢𝟘 : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
            ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
            ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
            ⦃ _ : LinMap A B {§} ⦄ {x : A}
         → f x ≢ 𝟘
            -------
         → x ≢ 𝟘
fx≢𝟘→x≢𝟘 = contraposition x≡𝟘→fx≡𝟘

-- Zero is unique output of linear map ≢ `const 𝟘`.
zero-unique : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
              ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
              ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
              ⦃ _ : LinMap A B {§} ⦄ ⦃ _ : ScalableCont A § ⦄
              {x : A}
           → Σ[ y ∈ A ] f y ≢ 𝟘
           → x ≢ 𝟘
              ------------------
           → f x ≢ 𝟘
zero-unique {§ = §} {x = x} (y , fy≢𝟘) x≢𝟘 =
  let y≢𝟘 : y ≢ 𝟘
      y≢𝟘 = fx≢𝟘→x≢𝟘 fy≢𝟘
      Σs→s·x≡y : Σ[ s ∈ § ] s · x ≡ y
      Σs→s·x≡y = cont x y
      Σs→fs·x≡fy : Σ[ s ∈ § ] f (s · x) ≡ f y
      Σs→fs·x≡fy = let (s , g) = Σs→s·x≡y
                     in (s , cong f g)
      Σs→s·fx≡fy : Σ[ s ∈ § ] s · f x ≡ f y
      Σs→s·fx≡fy = let (s , g) = Σs→fs·x≡fy
                     in (s , (begin
                               s · f x
                             ≡⟨ Eq.sym scales ⟩
                               f (s · x)
                             ≡⟨ g ⟩
                               f y
                             ∎))
      s·fx≢𝟘 : Σ[ s ∈ § ] s · f x ≢ 𝟘
      s·fx≢𝟘 = let (s , g) = Σs→s·fx≡fy
                in (s , λ s·fx≡𝟘 → fy≢𝟘 (step-≡ (f y) s·fx≡𝟘 (Eq.sym g)))
   in non-zeroʳ (snd s·fx≢𝟘)

-- ToDo: Can I prove this?
-- postulate
fx≡𝟘→x≡𝟘 : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
            ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
            ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
            ⦃ _ : LinMap A B {§} ⦄ ⦃ _ : ScalableCont A § ⦄
            {x : A}
         → Σ[ y ∈ A ] f y ≢ 𝟘
         → f x ≡ 𝟘
            -------
         → x ≡ 𝟘
fx≡𝟘→x≡𝟘 {x = x} Σ[y]fy≢𝟘 fx≡𝟘 =
  let x≡𝟘 : ¬ (x ≢ 𝟘)
      x≡𝟘 = λ x≢𝟘 → zero-unique Σ[y]fy≢𝟘 x≢𝟘 fx≡𝟘
   in ≡-involutive x≡𝟘

  
-- f (-x) ≡ - (f x)
fx+f-x≡𝟘 : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
           ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
           ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
           ⦃ _ : LinMap A B {§} ⦄ {x : A}
           -----------------
        → f x + f (- x) ≡ 𝟘
fx+f-x≡𝟘 {x = x} = begin
             f x + f (- x)
           ≡⟨ Eq.sym adds ⟩
             f (x - x)
           ≡⟨ cong f (-‿inverseʳ x) ⟩
             f 𝟘
           ≡⟨ f𝟘≡𝟘 {x = x} ⟩
             𝟘
           ∎

f-x≡-fx : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
          ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
          ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
          ⦃ _ : LinMap A B {§} ⦄ {x : A}
          -----------------
       → f (- x) ≡ - (f x)
f-x≡-fx {x = x} = uniqueʳ-⁻¹ (f x) (f (- x)) fx+f-x≡𝟘

-- A linear function is injective.
inj-lm : {A : Set ℓ₁} {B : Set ℓ₁} {§ : Set ℓ₁}
         ⦃ _ : Ring A ⦄ ⦃ _ : Ring B ⦄ ⦃ _ : Ring § ⦄
         ⦃ _ : Scalable A § ⦄ ⦃ _ : Scalable B § ⦄
         ⦃ _ : LinMap A B {§} ⦄ ⦃ _ : ScalableCont A § ⦄
         {x y : A}
      → Σ[ y ∈ A ] f y ≢ 𝟘
      → f x ≡ f y
         ------------------
      → x ≡ y
inj-lm {x = x} {y = y} Σ[y]fy≢𝟘 fx≡fy =
  let fx-fy≡𝟘 : f x + - f y ≡ 𝟘
      fx-fy≡𝟘 = begin
                  f x + - f y
                ≡⟨ cong (f x +_) (cong -_ (Eq.sym fx≡fy)) ⟩
                  f x + - f x
                ≡⟨ -‿inverseʳ (f x) ⟩
                  𝟘
                ∎
      fx-y≡𝟘 : f (x + - y) ≡ 𝟘
      fx-y≡𝟘 = begin
                   f (x + - y)
                 ≡⟨ adds ⟩
                   f x + f (- y)
                 ≡⟨ cong (f x +_) f-x≡-fx ⟩
                   f x + - f y
                 ≡⟨ fx-fy≡𝟘 ⟩
                   𝟘
                 ∎
      x-y≡𝟘 : x - y ≡ 𝟘
      x-y≡𝟘 = fx≡𝟘→x≡𝟘 {x = x - y} Σ[y]fy≢𝟘 fx-y≡𝟘
      x≡--y : x ≡ - (- y)
      x≡--y = uniqueˡ-⁻¹ x (- y) x-y≡𝟘
   in step-≡ x -‿involutive x≡--y

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

We define the "norm" of a vector as the reflexive inner product:
$|v| = v ⊙ v$.

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
    comm-⊙      : ∀ {a b : T}
                  -------------
               → a ⊙ b ≡ b ⊙ a
open VectorSpace ⦃ ... ⦄ public

x·z≡y·z→x≡y : {T : Set ℓ₁} {A : Set ℓ₁}
               ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
               ⦃ _ : Scalable T A ⦄ ⦃ _ : ScalableCont T A ⦄
               ⦃ _ : VectorSpace T A ⦄ ⦃ _ : LinMap T A ⦄
               {x y : T}
           → Σ[ y ∈ T ] f y ≢ 𝟘
           →  (∀ {z : T} → x ⊙ z ≡ y ⊙ z)
               ----------------------------
           →  x ≡ y
x·z≡y·z→x≡y {x = x} {y = y} Σ[y]fy≢𝟘 g =
  let z = foldl (λ acc v → acc + f v · v) 𝟘 basisSet
      x·z≡y·z = g {z}
      z·x≡y·z : z ⊙ x ≡ y ⊙ z
      z·x≡y·z = step-≡ (z ⊙ x) x·z≡y·z comm-⊙
      z·x≡z·y : z ⊙ x ≡ z ⊙ y
      z·x≡z·y = Eq.sym (step-≡ (z ⊙ y) (Eq.sym z·x≡y·z) comm-⊙)
      fx≡z·y : f x ≡ z ⊙ y
      fx≡z·y = step-≡ (f x) z·x≡z·y (Eq.sym orthonormal)
      fx≡fy : f x ≡ f y
      fx≡fy = Eq.sym (step-≡ (f y) (Eq.sym fx≡z·y) (Eq.sym orthonormal))
   in inj-lm Σ[y]fy≢𝟘 fx≡fy

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

a⊸§↔a : {T : Set ℓ₁} {A : Set ℓ₁}
         ⦃ _ : Ring T ⦄ ⦃ _ : Ring A ⦄
         ⦃ _ : Scalable T A ⦄ ⦃ _ : ScalableCont T A ⦄
         ⦃ _ : VectorSpace T A ⦄ ⦃ _ : LinMap T A ⦄
      → Σ[ y ∈ T ] f y ≢ 𝟘
         ---------------------------------------------
      → (LinMap T A) ↔ T
a⊸§↔a Σ[y]fy≢𝟘 =
  mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}
      ( (λ {x → begin
                  a⊸§→a (a⊸§←a x)
                ≡⟨⟩
                  a⊸§→a (mkLM (x ⊙_) ⊙-distrib-+ ⊙-comm-·)
                ≡⟨⟩
                  foldl (λ acc v → acc + (x ⊙ v) · v) 𝟘 basisSet
                ≡⟨ x·z≡y·z→x≡y Σ[y]fy≢𝟘 orthonormal ⟩
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

## Stashed

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

```
