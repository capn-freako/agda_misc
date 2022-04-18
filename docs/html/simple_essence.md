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

<pre class="Agda"><a id="5693" class="Keyword">module</a> <a id="5700" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5715" class="Keyword">where</a>

<a id="5722" class="Keyword">open</a> <a id="5727" class="Keyword">import</a> <a id="5734" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5753" class="Keyword">open</a> <a id="5758" class="Keyword">import</a> <a id="5765" href="Algebra.html" class="Module">Algebra</a>                            <a id="5800" class="Keyword">using</a> <a id="5806" class="Symbol">(</a><a id="5807" href="Algebra.Structures.html#12130" class="Record">IsRing</a><a id="5813" class="Symbol">;</a> <a id="5815" href="Algebra.Structures.html#7016" class="Record">IsNearSemiring</a><a id="5829" class="Symbol">)</a>
<a id="5831" class="Keyword">open</a> <a id="5836" class="Keyword">import</a> <a id="5843" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5878" class="Keyword">using</a> <a id="5884" class="Symbol">(</a><a id="5885" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5899" class="Symbol">)</a>
<a id="5901" class="Keyword">open</a> <a id="5906" class="Keyword">import</a> <a id="5913" href="Data.List.html" class="Module">Data.List</a>
<a id="5923" class="Keyword">open</a> <a id="5928" class="Keyword">import</a> <a id="5935" href="Data.Product.html" class="Module">Data.Product</a> <a id="5948" class="Keyword">using</a> <a id="5954" class="Symbol">(</a><a id="5955" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a><a id="5956" class="Symbol">;</a> <a id="5958" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a><a id="5961" class="Symbol">;</a> <a id="5963" href="Data.Product.html#1369" class="Function">∃</a><a id="5964" class="Symbol">;</a> <a id="5966" href="Data.Product.html#916" class="Function">Σ-syntax</a><a id="5974" class="Symbol">;</a> <a id="5976" href="Data.Product.html#1788" class="Function">∃-syntax</a><a id="5984" class="Symbol">)</a>
<a id="5986" class="Keyword">open</a> <a id="5991" class="Keyword">import</a> <a id="5998" href="Function.html" class="Module">Function</a>     <a id="6011" class="Keyword">using</a> <a id="6017" class="Symbol">(</a><a id="6018" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="6021" class="Symbol">;</a> <a id="6023" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="6026" class="Symbol">;</a> <a id="6028" href="Function.Base.html#615" class="Function">id</a><a id="6030" class="Symbol">;</a> <a id="6032" href="Function.Base.html#636" class="Function">const</a><a id="6037" class="Symbol">)</a>
<a id="6039" class="Keyword">open</a> <a id="6044" class="Keyword">import</a> <a id="6051" href="Level.html" class="Module">Level</a>        <a id="6064" class="Keyword">using</a> <a id="6070" class="Symbol">(</a><a id="6071" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="6076" class="Symbol">;</a> <a id="6078" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="6081" class="Symbol">)</a>

<a id="6084" class="Keyword">import</a> <a id="6091" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="6129" class="Symbol">as</a> <a id="6132" class="Module">Eq</a>
<a id="6135" class="Keyword">open</a> <a id="6140" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="6143" class="Keyword">using</a> <a id="6149" class="Symbol">(</a><a id="6150" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="6153" class="Symbol">;</a> <a id="6155" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="6159" class="Symbol">;</a> <a id="6161" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="6166" class="Symbol">;</a> <a id="6168" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="6171" class="Symbol">;</a> <a id="6173" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="6177" class="Symbol">;</a> <a id="6179" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="6184" class="Symbol">;</a> <a id="6186" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="6194" class="Symbol">;</a> <a id="6196" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="6201" class="Symbol">;</a> <a id="6203" href="Relation.Binary.PropositionalEquality.Core.html#840" class="Function Operator">_≢_</a><a id="6206" class="Symbol">)</a>
<a id="6208" class="Keyword">open</a> <a id="6213" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a>                   <a id="6246" class="Keyword">using</a> <a id="6252" class="Symbol">(</a><a id="6253" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="6259" class="Symbol">;</a> <a id="6261" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="6266" class="Symbol">;</a> <a id="6268" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="6274" class="Symbol">;</a> <a id="6276" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="6278" class="Symbol">)</a>
<a id="6280" class="Keyword">open</a> <a id="6285" class="Keyword">import</a> <a id="6292" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>          <a id="6318" class="Keyword">using</a> <a id="6324" class="Symbol">(</a><a id="6325" href="Relation.Nullary.html#653" class="Function Operator">¬_</a><a id="6327" class="Symbol">)</a>
<a id="6329" class="Keyword">open</a> <a id="6334" class="Keyword">import</a> <a id="6341" href="Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="6367" class="Keyword">using</a> <a id="6373" class="Symbol">(</a><a id="6374" href="Relation.Nullary.Negation.html#929" class="Function">contraposition</a><a id="6388" class="Symbol">)</a>

<a id="6391" class="Keyword">variable</a>
  <a id="6402" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a> <a id="6405" href="simple_essence.html#6405" class="Generalizable">ℓ₂</a> <a id="6408" href="simple_essence.html#6408" class="Generalizable">ℓ₃</a> <a id="6411" class="Symbol">:</a> <a id="6413" href="Agda.Primitive.html#423" class="Postulate">Level</a>
  
<a id="6422" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="6434" href="simple_essence.html#6434" class="Postulate">extensionality</a> <a id="6449" class="Symbol">:</a> <a id="6451" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="6466" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a> <a id="6469" href="simple_essence.html#6405" class="Generalizable">ℓ₂</a>

</pre>
### Type Classes

Here, we define the abstract type classes we'll be using in our proofs.
We use a slight variation on the approach taken in the standard library "bundles", because it yields cleaner, more succinct, abstract code capable of _automatic instance selection_.

**Note:** We've removed our previously defined custom typeclass: `Additive`, in favor of `Ring` defined in the Agda standard library.
We've kept `Scalable`, for now, in order to get some incremental progress working and checked in before attempting to use `Module` and friends.

<pre class="Agda"><a id="7038" class="Keyword">record</a> <a id="Scalable"></a><a id="7045" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="7054" class="Symbol">(</a><a id="7055" href="simple_essence.html#7055" class="Bound">T</a> <a id="7057" class="Symbol">:</a> <a id="7059" class="PrimitiveType">Set</a> <a id="7063" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="7065" class="Symbol">)</a> <a id="7067" class="Symbol">(</a><a id="7068" href="simple_essence.html#7068" class="Bound">A</a> <a id="7070" class="Symbol">:</a> <a id="7072" class="PrimitiveType">Set</a> <a id="7076" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="7078" class="Symbol">)</a> <a id="7080" class="Symbol">:</a> <a id="7082" class="PrimitiveType">Set</a> <a id="7086" class="Symbol">(</a><a id="7087" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="7097" href="simple_essence.html#7063" class="Bound">ℓ₁</a><a id="7099" class="Symbol">)</a> <a id="7101" class="Keyword">where</a>
  <a id="7109" class="Keyword">infix</a> <a id="7115" class="Number">7</a> <a id="7117" href="simple_essence.html#7133" class="Field Operator">_·_</a>
  <a id="7123" class="Keyword">field</a>
    <a id="Scalable._·_"></a><a id="7133" href="simple_essence.html#7133" class="Field Operator">_·_</a> <a id="7137" class="Symbol">:</a> <a id="7139" href="simple_essence.html#7068" class="Bound">A</a> <a id="7141" class="Symbol">→</a> <a id="7143" href="simple_essence.html#7055" class="Bound">T</a> <a id="7145" class="Symbol">→</a> <a id="7147" href="simple_essence.html#7055" class="Bound">T</a>
<a id="7149" class="Keyword">open</a> <a id="7154" href="simple_essence.html#7045" class="Module">Scalable</a> <a id="7163" class="Symbol">⦃</a> <a id="7165" class="Symbol">...</a> <a id="7169" class="Symbol">⦄</a> <a id="7171" class="Keyword">public</a>

<a id="7179" class="Keyword">record</a> <a id="Ring"></a><a id="7186" href="simple_essence.html#7186" class="Record">Ring</a> <a id="7191" class="Symbol">(</a><a id="7192" href="simple_essence.html#7192" class="Bound">A</a> <a id="7194" class="Symbol">:</a> <a id="7196" class="PrimitiveType">Set</a> <a id="7200" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="7202" class="Symbol">)</a> <a id="7204" class="Symbol">:</a> <a id="7206" class="PrimitiveType">Set</a> <a id="7210" class="Symbol">(</a><a id="7211" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="7221" href="simple_essence.html#7200" class="Bound">ℓ₁</a><a id="7223" class="Symbol">)</a> <a id="7225" class="Keyword">where</a>
  <a id="7233" class="Keyword">infixl</a> <a id="7240" class="Number">6</a> <a id="7242" href="simple_essence.html#7287" class="Field Operator">_+_</a>
  <a id="7248" class="Keyword">infixl</a> <a id="7255" class="Number">7</a> <a id="7257" href="simple_essence.html#7307" class="Field Operator">_*_</a>
  <a id="7263" class="Keyword">infix</a>  <a id="7270" class="Number">8</a> <a id="7272" href="simple_essence.html#7327" class="Field Operator">-_</a>
  <a id="7277" class="Keyword">field</a>
    <a id="Ring._+_"></a><a id="7287" href="simple_essence.html#7287" class="Field Operator">_+_</a> <a id="7291" class="Symbol">:</a> <a id="7293" href="simple_essence.html#7192" class="Bound">A</a> <a id="7295" class="Symbol">→</a> <a id="7297" href="simple_essence.html#7192" class="Bound">A</a> <a id="7299" class="Symbol">→</a> <a id="7301" href="simple_essence.html#7192" class="Bound">A</a>
    <a id="Ring._*_"></a><a id="7307" href="simple_essence.html#7307" class="Field Operator">_*_</a> <a id="7311" class="Symbol">:</a> <a id="7313" href="simple_essence.html#7192" class="Bound">A</a> <a id="7315" class="Symbol">→</a> <a id="7317" href="simple_essence.html#7192" class="Bound">A</a> <a id="7319" class="Symbol">→</a> <a id="7321" href="simple_essence.html#7192" class="Bound">A</a>
    <a id="Ring.-_"></a><a id="7327" href="simple_essence.html#7327" class="Field Operator">-_</a>  <a id="7331" class="Symbol">:</a> <a id="7333" href="simple_essence.html#7192" class="Bound">A</a> <a id="7335" class="Symbol">→</a> <a id="7337" href="simple_essence.html#7192" class="Bound">A</a>
    <a id="Ring.𝟘"></a><a id="7343" href="simple_essence.html#7343" class="Field">𝟘</a>   <a id="7347" class="Symbol">:</a> <a id="7349" href="simple_essence.html#7192" class="Bound">A</a>
    <a id="Ring.𝟙"></a><a id="7355" href="simple_essence.html#7355" class="Field">𝟙</a>   <a id="7359" class="Symbol">:</a> <a id="7361" href="simple_essence.html#7192" class="Bound">A</a>
    <a id="7367" class="Symbol">⦃</a> <a id="Ring.isRing"></a><a id="7369" href="simple_essence.html#7369" class="Field">isRing</a> <a id="7376" class="Symbol">⦄</a> <a id="7378" class="Symbol">:</a> <a id="7380" href="Algebra.Structures.html#12130" class="Record">IsRing</a> <a id="7387" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="7391" href="simple_essence.html#7287" class="Field Operator">_+_</a> <a id="7395" href="simple_essence.html#7307" class="Field Operator">_*_</a> <a id="7399" href="simple_essence.html#7327" class="Field Operator">-_</a> <a id="7402" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="7404" href="simple_essence.html#7355" class="Field">𝟙</a>
  <a id="7408" class="Keyword">open</a> <a id="7413" href="Algebra.Structures.html#12130" class="Module">IsRing</a> <a id="7420" href="simple_essence.html#7369" class="Field">isRing</a> <a id="7427" class="Keyword">public</a>
  <a id="7436" class="Keyword">instance</a>
    <a id="Ring.scalableRing"></a><a id="7449" href="simple_essence.html#7449" class="Function">scalableRing</a> <a id="7462" class="Symbol">:</a> <a id="7464" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="7473" href="simple_essence.html#7192" class="Bound">A</a> <a id="7475" href="simple_essence.html#7192" class="Bound">A</a>
    <a id="7481" href="simple_essence.html#7449" class="Function">scalableRing</a> <a id="7494" class="Symbol">=</a> <a id="7496" class="Keyword">record</a>
      <a id="7509" class="Symbol">{</a> <a id="7511" href="simple_essence.html#7133" class="Field Operator">_·_</a> <a id="7515" class="Symbol">=</a> <a id="7517" href="simple_essence.html#7307" class="Field Operator">_*_</a>
      <a id="7527" class="Symbol">}</a>
  <a id="7531" class="Keyword">open</a> <a id="7536" href="simple_essence.html#7045" class="Module">Scalable</a> <a id="7545" href="simple_essence.html#7449" class="Function">scalableRing</a>
<a id="7558" class="Keyword">open</a> <a id="7563" href="simple_essence.html#7186" class="Module">Ring</a> <a id="7568" class="Symbol">⦃</a> <a id="7570" class="Symbol">...</a> <a id="7574" class="Symbol">⦄</a> <a id="7576" class="Keyword">public</a>
    
</pre>
### Linear Maps

Here, we capture our intended meaning of _linearity_.

We take the vector-centric definition offered by Conal in his paper:

> A linear map is one that distributes over _vector_ addition and _scalar_ multiplication.

<pre class="Agda"><a id="7835" class="Keyword">record</a> <a id="LinMap"></a><a id="7842" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="7849" class="Symbol">(</a><a id="7850" href="simple_essence.html#7850" class="Bound">A</a> <a id="7852" class="Symbol">:</a> <a id="7854" class="PrimitiveType">Set</a> <a id="7858" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="7860" class="Symbol">)</a> <a id="7862" class="Symbol">(</a><a id="7863" href="simple_essence.html#7863" class="Bound">B</a> <a id="7865" class="Symbol">:</a> <a id="7867" class="PrimitiveType">Set</a> <a id="7871" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="7873" class="Symbol">)</a> <a id="7875" class="Symbol">{</a><a id="7876" href="simple_essence.html#7876" class="Bound">§</a> <a id="7878" class="Symbol">:</a> <a id="7880" class="PrimitiveType">Set</a> <a id="7884" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="7886" class="Symbol">}</a>
              <a id="7902" class="Symbol">⦃</a> <a id="7904" href="simple_essence.html#7904" class="Bound">_</a> <a id="7906" class="Symbol">:</a> <a id="7908" href="simple_essence.html#7186" class="Record">Ring</a> <a id="7913" href="simple_essence.html#7850" class="Bound">A</a> <a id="7915" class="Symbol">⦄</a> <a id="7917" class="Symbol">⦃</a> <a id="7919" href="simple_essence.html#7919" class="Bound">_</a> <a id="7921" class="Symbol">:</a> <a id="7923" href="simple_essence.html#7186" class="Record">Ring</a> <a id="7928" href="simple_essence.html#7863" class="Bound">B</a> <a id="7930" class="Symbol">⦄</a>
              <a id="7946" class="Symbol">⦃</a> <a id="7948" href="simple_essence.html#7948" class="Bound">_</a> <a id="7950" class="Symbol">:</a> <a id="7952" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="7961" href="simple_essence.html#7850" class="Bound">A</a> <a id="7963" href="simple_essence.html#7876" class="Bound">§</a> <a id="7965" class="Symbol">⦄</a>   <a id="7969" class="Symbol">⦃</a> <a id="7971" href="simple_essence.html#7971" class="Bound">_</a> <a id="7973" class="Symbol">:</a> <a id="7975" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="7984" href="simple_essence.html#7863" class="Bound">B</a> <a id="7986" href="simple_essence.html#7876" class="Bound">§</a> <a id="7988" class="Symbol">⦄</a>
              <a id="8004" class="Symbol">:</a> <a id="8006" class="PrimitiveType">Set</a> <a id="8010" href="simple_essence.html#7858" class="Bound">ℓ₁</a> <a id="8013" class="Keyword">where</a>
  <a id="8021" class="Keyword">constructor</a> <a id="mkLM"></a><a id="8033" href="simple_essence.html#8033" class="InductiveConstructor">mkLM</a>
  <a id="8040" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="8050" href="simple_essence.html#8050" class="Field">f</a>      <a id="8057" class="Symbol">:</a> <a id="8059" href="simple_essence.html#7850" class="Bound">A</a> <a id="8061" class="Symbol">→</a> <a id="8063" href="simple_essence.html#7863" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="8070" href="simple_essence.html#8070" class="Field">adds</a>   <a id="8077" class="Symbol">:</a> <a id="8079" class="Symbol">∀</a> <a id="8081" class="Symbol">{</a><a id="8082" href="simple_essence.html#8082" class="Bound">a</a> <a id="8084" href="simple_essence.html#8084" class="Bound">b</a> <a id="8086" class="Symbol">:</a> <a id="8088" href="simple_essence.html#7850" class="Bound">A</a><a id="8089" class="Symbol">}</a>
             <a id="8104" class="Comment">---------------------</a>
          <a id="8136" class="Symbol">→</a> <a id="8138" href="simple_essence.html#8050" class="Field">f</a> <a id="8140" class="Symbol">(</a><a id="8141" href="simple_essence.html#8082" class="Bound">a</a> <a id="8143" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="8145" href="simple_essence.html#8084" class="Bound">b</a><a id="8146" class="Symbol">)</a> <a id="8148" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8150" href="simple_essence.html#8050" class="Field">f</a> <a id="8152" href="simple_essence.html#8082" class="Bound">a</a> <a id="8154" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="8156" href="simple_essence.html#8050" class="Field">f</a> <a id="8158" href="simple_essence.html#8084" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="8165" href="simple_essence.html#8165" class="Field">scales</a> <a id="8172" class="Symbol">:</a> <a id="8174" class="Symbol">∀</a> <a id="8176" class="Symbol">{</a><a id="8177" href="simple_essence.html#8177" class="Bound">s</a> <a id="8179" class="Symbol">:</a> <a id="8181" href="simple_essence.html#7876" class="Bound">§</a><a id="8182" class="Symbol">}</a> <a id="8184" class="Symbol">{</a><a id="8185" href="simple_essence.html#8185" class="Bound">a</a> <a id="8187" class="Symbol">:</a> <a id="8189" href="simple_essence.html#7850" class="Bound">A</a><a id="8190" class="Symbol">}</a>
             <a id="8205" class="Comment">-------------------</a>
          <a id="8235" class="Symbol">→</a> <a id="8237" href="simple_essence.html#8050" class="Field">f</a> <a id="8239" class="Symbol">(</a><a id="8240" href="simple_essence.html#8177" class="Bound">s</a> <a id="8242" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="8244" href="simple_essence.html#8185" class="Bound">a</a><a id="8245" class="Symbol">)</a> <a id="8247" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8249" href="simple_essence.html#8177" class="Bound">s</a> <a id="8251" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="8253" href="simple_essence.html#8050" class="Field">f</a> <a id="8255" href="simple_essence.html#8185" class="Bound">a</a>

<a id="8258" class="Keyword">open</a> <a id="8263" href="simple_essence.html#7842" class="Module">LinMap</a> <a id="8270" class="Symbol">⦃</a> <a id="8272" class="Symbol">...</a> <a id="8276" class="Symbol">⦄</a> <a id="8278" class="Keyword">public</a>

<a id="8286" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="8312" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="8360" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="8372" href="simple_essence.html#8372" class="Postulate">⊸≡</a> <a id="8375" class="Symbol">:</a> <a id="8377" class="Symbol">{</a><a id="8378" href="simple_essence.html#8378" class="Bound">A</a> <a id="8380" class="Symbol">:</a> <a id="8382" class="PrimitiveType">Set</a> <a id="8386" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="8388" class="Symbol">}</a> <a id="8390" class="Symbol">{</a><a id="8391" href="simple_essence.html#8391" class="Bound">B</a> <a id="8393" class="Symbol">:</a> <a id="8395" class="PrimitiveType">Set</a> <a id="8399" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="8401" class="Symbol">}</a> <a id="8403" class="Symbol">{</a><a id="8404" href="simple_essence.html#8404" class="Bound">§</a> <a id="8406" class="Symbol">:</a> <a id="8408" class="PrimitiveType">Set</a> <a id="8412" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="8414" class="Symbol">}</a>
       <a id="8423" class="Symbol">⦃</a> <a id="8425" href="simple_essence.html#8425" class="Bound">_</a> <a id="8427" class="Symbol">:</a> <a id="8429" href="simple_essence.html#7186" class="Record">Ring</a> <a id="8434" href="simple_essence.html#8378" class="Bound">A</a> <a id="8436" class="Symbol">⦄</a> <a id="8438" class="Symbol">⦃</a> <a id="8440" href="simple_essence.html#8440" class="Bound">_</a> <a id="8442" class="Symbol">:</a> <a id="8444" href="simple_essence.html#7186" class="Record">Ring</a> <a id="8449" href="simple_essence.html#8391" class="Bound">B</a> <a id="8451" class="Symbol">⦄</a>
       <a id="8460" class="Symbol">⦃</a> <a id="8462" href="simple_essence.html#8462" class="Bound">_</a> <a id="8464" class="Symbol">:</a> <a id="8466" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="8475" href="simple_essence.html#8378" class="Bound">A</a> <a id="8477" href="simple_essence.html#8404" class="Bound">§</a> <a id="8479" class="Symbol">⦄</a> <a id="8481" class="Symbol">⦃</a> <a id="8483" href="simple_essence.html#8483" class="Bound">_</a> <a id="8485" class="Symbol">:</a> <a id="8487" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="8496" href="simple_essence.html#8391" class="Bound">B</a> <a id="8498" href="simple_essence.html#8404" class="Bound">§</a> <a id="8500" class="Symbol">⦄</a>
       <a id="8509" class="Symbol">{</a><a id="8510" href="simple_essence.html#8510" class="Bound">lm₁</a> <a id="8514" href="simple_essence.html#8514" class="Bound">lm₂</a> <a id="8518" class="Symbol">:</a> <a id="8520" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="8527" href="simple_essence.html#8378" class="Bound">A</a> <a id="8529" href="simple_essence.html#8391" class="Bound">B</a> <a id="8531" class="Symbol">{</a><a id="8532" href="simple_essence.html#8404" class="Bound">§</a><a id="8533" class="Symbol">}}</a>
    <a id="8540" class="Symbol">→</a> <a id="8542" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="8551" href="simple_essence.html#8510" class="Bound">lm₁</a> <a id="8555" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8557" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="8566" href="simple_essence.html#8514" class="Bound">lm₂</a>
       <a id="8577" class="Comment">--------------------------</a>
    <a id="8608" class="Symbol">→</a> <a id="8610" href="simple_essence.html#8510" class="Bound">lm₁</a> <a id="8614" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8616" href="simple_essence.html#8514" class="Bound">lm₂</a>

</pre>
### Vector Spaces

Here, we define what we mean by a _vector space_.

In its most general sense, a "vector space" provides a function that takes some _index_ type and uses it to map from some _container_ type to a single value of the _carrier_ type.

We add a few extras, useful when doing _linear algebra_:

Vector Addition
    : We can "add" two vectors, producing a third.

Scalar Multiplication
    : We can "scale" a vector by an element of the carrier type, producing another vector.

Inner Product
    : We can combine two vectors, producing a single value of the carrier type.

**Note:** The remaining definitions in the code below were the result of attempting to solve the first isomorphism.

**Note:** We use `Ring`, as opposed to a `SemiRing`, because that gives us _subtraction_, which allows us to prove _injectivity_ of linear maps, which in turn allows us to replace the `x·z≡y·z→x≡y` _postulate_ with an equivalent _proof_.

<pre class="Agda"><a id="9576" class="Keyword">record</a> <a id="VectorSpace"></a><a id="9583" href="simple_essence.html#9583" class="Record">VectorSpace</a>
  <a id="9597" class="Symbol">(</a><a id="9598" href="simple_essence.html#9598" class="Bound">T</a> <a id="9600" class="Symbol">:</a> <a id="9602" class="PrimitiveType">Set</a> <a id="9606" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="9608" class="Symbol">)</a> <a id="9610" class="Symbol">(</a><a id="9611" href="simple_essence.html#9611" class="Bound">A</a> <a id="9613" class="Symbol">:</a> <a id="9615" class="PrimitiveType">Set</a> <a id="9619" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="9621" class="Symbol">)</a>
  <a id="9625" class="Symbol">⦃</a> <a id="9627" href="simple_essence.html#9627" class="Bound">_</a> <a id="9629" class="Symbol">:</a> <a id="9631" href="simple_essence.html#7186" class="Record">Ring</a> <a id="9636" href="simple_essence.html#9598" class="Bound">T</a> <a id="9638" class="Symbol">⦄</a> <a id="9640" class="Symbol">⦃</a> <a id="9642" href="simple_essence.html#9642" class="Bound">_</a> <a id="9644" class="Symbol">:</a> <a id="9646" href="simple_essence.html#7186" class="Record">Ring</a> <a id="9651" href="simple_essence.html#9611" class="Bound">A</a> <a id="9653" class="Symbol">⦄</a> <a id="9655" class="Symbol">⦃</a> <a id="9657" href="simple_essence.html#9657" class="Bound">_</a> <a id="9659" class="Symbol">:</a> <a id="9661" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="9670" href="simple_essence.html#9598" class="Bound">T</a> <a id="9672" href="simple_essence.html#9611" class="Bound">A</a> <a id="9674" class="Symbol">⦄</a>
  <a id="9678" class="Symbol">:</a> <a id="9680" class="PrimitiveType">Set</a> <a id="9684" class="Symbol">(</a><a id="9685" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="9695" href="simple_essence.html#9606" class="Bound">ℓ₁</a><a id="9697" class="Symbol">)</a> <a id="9699" class="Keyword">where</a>
  <a id="9707" class="Keyword">infix</a>  <a id="9714" class="Number">7</a> <a id="9716" href="simple_essence.html#9798" class="Field Operator">_⊙_</a>
  <a id="9722" class="Keyword">field</a>
    <a id="VectorSpace.I"></a><a id="9732" href="simple_essence.html#9732" class="Field">I</a>     <a id="9738" class="Symbol">:</a> <a id="9740" class="PrimitiveType">Set</a> <a id="9744" href="simple_essence.html#9606" class="Bound">ℓ₁</a>
    <a id="VectorSpace.index"></a><a id="9751" href="simple_essence.html#9751" class="Field">index</a> <a id="9757" class="Symbol">:</a> <a id="9759" href="simple_essence.html#9732" class="Field">I</a> <a id="9761" class="Symbol">→</a> <a id="9763" href="simple_essence.html#9598" class="Bound">T</a> <a id="9765" class="Symbol">→</a> <a id="9767" href="simple_essence.html#9611" class="Bound">A</a>
    <a id="VectorSpace.basisSet"></a><a id="9773" href="simple_essence.html#9773" class="Field">basisSet</a>    <a id="9785" class="Symbol">:</a> <a id="9787" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="9792" href="simple_essence.html#9598" class="Bound">T</a>
    <a id="VectorSpace._⊙_"></a><a id="9798" href="simple_essence.html#9798" class="Field Operator">_⊙_</a>         <a id="9810" class="Symbol">:</a> <a id="9812" href="simple_essence.html#9598" class="Bound">T</a> <a id="9814" class="Symbol">→</a> <a id="9816" href="simple_essence.html#9598" class="Bound">T</a> <a id="9818" class="Symbol">→</a> <a id="9820" href="simple_essence.html#9611" class="Bound">A</a>
    <a id="9826" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.⊙-distrib-+"></a><a id="9876" href="simple_essence.html#9876" class="Field">⊙-distrib-+</a> <a id="9888" class="Symbol">:</a> <a id="9890" class="Symbol">∀</a> <a id="9892" class="Symbol">{</a><a id="9893" href="simple_essence.html#9893" class="Bound">a</a> <a id="9895" href="simple_essence.html#9895" class="Bound">b</a> <a id="9897" href="simple_essence.html#9897" class="Bound">c</a> <a id="9899" class="Symbol">:</a> <a id="9901" href="simple_essence.html#9598" class="Bound">T</a><a id="9902" class="Symbol">}</a>
                  <a id="9922" class="Comment">-------------------------------</a>
               <a id="9969" class="Symbol">→</a> <a id="9971" href="simple_essence.html#9893" class="Bound">a</a> <a id="9973" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="9975" class="Symbol">(</a><a id="9976" href="simple_essence.html#9895" class="Bound">b</a> <a id="9978" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="9980" href="simple_essence.html#9897" class="Bound">c</a><a id="9981" class="Symbol">)</a> <a id="9983" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9985" class="Symbol">(</a><a id="9986" href="simple_essence.html#9893" class="Bound">a</a> <a id="9988" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="9990" href="simple_essence.html#9895" class="Bound">b</a><a id="9991" class="Symbol">)</a> <a id="9993" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="9995" class="Symbol">(</a><a id="9996" href="simple_essence.html#9893" class="Bound">a</a> <a id="9998" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="10000" href="simple_essence.html#9897" class="Bound">c</a><a id="10001" class="Symbol">)</a>
    <a id="VectorSpace.⊙-comm-·"></a><a id="10007" href="simple_essence.html#10007" class="Field">⊙-comm-·</a>    <a id="10019" class="Symbol">:</a> <a id="10021" class="Symbol">∀</a> <a id="10023" class="Symbol">{</a><a id="10024" href="simple_essence.html#10024" class="Bound">s</a> <a id="10026" class="Symbol">:</a> <a id="10028" href="simple_essence.html#9611" class="Bound">A</a><a id="10029" class="Symbol">}</a> <a id="10031" class="Symbol">{</a><a id="10032" href="simple_essence.html#10032" class="Bound">a</a> <a id="10034" href="simple_essence.html#10034" class="Bound">b</a> <a id="10036" class="Symbol">:</a> <a id="10038" href="simple_essence.html#9598" class="Bound">T</a><a id="10039" class="Symbol">}</a>
                  <a id="10059" class="Comment">-------------------------</a>
               <a id="10100" class="Symbol">→</a> <a id="10102" href="simple_essence.html#10032" class="Bound">a</a> <a id="10104" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="10106" class="Symbol">(</a><a id="10107" href="simple_essence.html#10024" class="Bound">s</a> <a id="10109" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10111" href="simple_essence.html#10034" class="Bound">b</a><a id="10112" class="Symbol">)</a> <a id="10114" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10116" href="simple_essence.html#10024" class="Bound">s</a> <a id="10118" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10120" class="Symbol">(</a><a id="10121" href="simple_essence.html#10032" class="Bound">a</a> <a id="10123" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="10125" href="simple_essence.html#10034" class="Bound">b</a><a id="10126" class="Symbol">)</a>
    <a id="VectorSpace.orthonormal"></a><a id="10132" href="simple_essence.html#10132" class="Field">orthonormal</a> <a id="10144" class="Symbol">:</a> <a id="10146" class="Symbol">∀</a> <a id="10148" class="Symbol">{</a><a id="10149" href="simple_essence.html#10149" class="Bound">f</a> <a id="10151" class="Symbol">:</a> <a id="10153" href="simple_essence.html#9598" class="Bound">T</a> <a id="10155" class="Symbol">→</a> <a id="10157" href="simple_essence.html#9611" class="Bound">A</a><a id="10158" class="Symbol">}</a>
               <a id="10175" class="Symbol">→</a> <a id="10177" class="Symbol">{</a><a id="10178" href="simple_essence.html#10178" class="Bound">x</a> <a id="10180" class="Symbol">:</a> <a id="10182" href="simple_essence.html#9598" class="Bound">T</a><a id="10183" class="Symbol">}</a>
                  <a id="10203" class="Comment">------------------------------------</a>
               <a id="10255" class="Symbol">→</a> <a id="10257" class="Symbol">(</a> <a id="10259" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10265" class="Symbol">(λ</a> <a id="10268" href="simple_essence.html#10268" class="Bound">acc</a> <a id="10272" href="simple_essence.html#10272" class="Bound">v</a> <a id="10274" class="Symbol">→</a> <a id="10276" href="simple_essence.html#10268" class="Bound">acc</a> <a id="10280" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="10282" class="Symbol">(</a><a id="10283" href="simple_essence.html#10149" class="Bound">f</a> <a id="10285" href="simple_essence.html#10272" class="Bound">v</a><a id="10286" class="Symbol">)</a> <a id="10288" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10290" href="simple_essence.html#10272" class="Bound">v</a><a id="10291" class="Symbol">)</a>
                          <a id="10319" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="10321" href="simple_essence.html#9773" class="Field">basisSet</a>
                  <a id="10348" class="Symbol">)</a> <a id="10350" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="10352" href="simple_essence.html#10178" class="Bound">x</a> <a id="10354" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10356" href="simple_essence.html#10149" class="Bound">f</a> <a id="10358" href="simple_essence.html#10178" class="Bound">x</a>
<a id="10360" class="Keyword">open</a> <a id="10365" href="simple_essence.html#9583" class="Module">VectorSpace</a> <a id="10377" class="Symbol">⦃</a> <a id="10379" class="Symbol">...</a> <a id="10383" class="Symbol">⦄</a> <a id="10385" class="Keyword">public</a>

</pre>
### Isomorphism 1: `(A ⊸ s) ↔ A`

Here, I prove that a linear map from some "vector" type `T` to a scalar of its _carrier_ type `A` is isomorphic to `T`.

<pre class="Agda"><a id="a⊸§→a"></a><a id="10561" href="simple_essence.html#10561" class="Function">a⊸§→a</a> <a id="10567" class="Symbol">:</a> <a id="10569" class="Symbol">{</a><a id="10570" href="simple_essence.html#10570" class="Bound">T</a> <a id="10572" class="Symbol">:</a> <a id="10574" class="PrimitiveType">Set</a> <a id="10578" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10580" class="Symbol">}</a> <a id="10582" class="Symbol">{</a><a id="10583" href="simple_essence.html#10583" class="Bound">A</a> <a id="10585" class="Symbol">:</a> <a id="10587" class="PrimitiveType">Set</a> <a id="10591" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10593" class="Symbol">}</a>
         <a id="10604" class="Symbol">⦃</a> <a id="10606" href="simple_essence.html#10606" class="Bound">_</a> <a id="10608" class="Symbol">:</a> <a id="10610" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10615" href="simple_essence.html#10570" class="Bound">T</a> <a id="10617" class="Symbol">⦄</a> <a id="10619" class="Symbol">⦃</a> <a id="10621" href="simple_essence.html#10621" class="Bound">_</a> <a id="10623" class="Symbol">:</a> <a id="10625" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10630" href="simple_essence.html#10583" class="Bound">A</a> <a id="10632" class="Symbol">⦄</a>
         <a id="10643" class="Symbol">⦃</a> <a id="10645" href="simple_essence.html#10645" class="Bound">_</a> <a id="10647" class="Symbol">:</a> <a id="10649" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="10658" href="simple_essence.html#10570" class="Bound">T</a> <a id="10660" href="simple_essence.html#10583" class="Bound">A</a> <a id="10662" class="Symbol">⦄</a>
         <a id="10673" class="Symbol">⦃</a> <a id="10675" href="simple_essence.html#10675" class="Bound">_</a> <a id="10677" class="Symbol">:</a> <a id="10679" href="simple_essence.html#9583" class="Record">VectorSpace</a> <a id="10691" href="simple_essence.html#10570" class="Bound">T</a> <a id="10693" href="simple_essence.html#10583" class="Bound">A</a> <a id="10695" class="Symbol">⦄</a>
         <a id="10706" class="Comment">------------------------------</a>
      <a id="10743" class="Symbol">→</a> <a id="10745" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="10752" href="simple_essence.html#10570" class="Bound">T</a> <a id="10754" href="simple_essence.html#10583" class="Bound">A</a> <a id="10756" class="Symbol">{</a><a id="10757" href="simple_essence.html#10583" class="Bound">A</a><a id="10758" class="Symbol">}</a> <a id="10760" class="Symbol">→</a> <a id="10762" href="simple_essence.html#10570" class="Bound">T</a>
<a id="10764" href="simple_essence.html#10561" class="Function">a⊸§→a</a> <a id="10770" class="Symbol">=</a> <a id="10772" class="Symbol">λ</a> <a id="10774" class="Symbol">{</a> <a id="10776" href="simple_essence.html#10776" class="Bound">lm</a> <a id="10779" class="Symbol">→</a> <a id="10781" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10787" class="Symbol">(λ</a> <a id="10790" href="simple_essence.html#10790" class="Bound">acc</a> <a id="10794" href="simple_essence.html#10794" class="Bound">v</a> <a id="10796" class="Symbol">→</a>
                     <a id="10819" href="simple_essence.html#10790" class="Bound">acc</a> <a id="10823" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="10825" class="Symbol">(</a><a id="10826" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="10835" href="simple_essence.html#10776" class="Bound">lm</a> <a id="10838" href="simple_essence.html#10794" class="Bound">v</a><a id="10839" class="Symbol">)</a> <a id="10841" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10843" href="simple_essence.html#10794" class="Bound">v</a><a id="10844" class="Symbol">)</a> <a id="10846" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="10848" href="simple_essence.html#9773" class="Field">basisSet</a> <a id="10857" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="10860" href="simple_essence.html#10860" class="Function">a⊸§←a</a> <a id="10866" class="Symbol">:</a> <a id="10868" class="Symbol">{</a><a id="10869" href="simple_essence.html#10869" class="Bound">T</a> <a id="10871" class="Symbol">:</a> <a id="10873" class="PrimitiveType">Set</a> <a id="10877" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10879" class="Symbol">}</a> <a id="10881" class="Symbol">{</a><a id="10882" href="simple_essence.html#10882" class="Bound">A</a> <a id="10884" class="Symbol">:</a> <a id="10886" class="PrimitiveType">Set</a> <a id="10890" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10892" class="Symbol">}</a>
         <a id="10903" class="Symbol">⦃</a> <a id="10905" href="simple_essence.html#10905" class="Bound">_</a> <a id="10907" class="Symbol">:</a> <a id="10909" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10914" href="simple_essence.html#10869" class="Bound">T</a> <a id="10916" class="Symbol">⦄</a> <a id="10918" class="Symbol">⦃</a> <a id="10920" href="simple_essence.html#10920" class="Bound">_</a> <a id="10922" class="Symbol">:</a> <a id="10924" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10929" href="simple_essence.html#10882" class="Bound">A</a> <a id="10931" class="Symbol">⦄</a>
         <a id="10942" class="Symbol">⦃</a> <a id="10944" href="simple_essence.html#10944" class="Bound">_</a> <a id="10946" class="Symbol">:</a> <a id="10948" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="10957" href="simple_essence.html#10869" class="Bound">T</a> <a id="10959" href="simple_essence.html#10882" class="Bound">A</a> <a id="10961" class="Symbol">⦄</a>
         <a id="10972" class="Symbol">⦃</a> <a id="10974" href="simple_essence.html#10974" class="Bound">_</a> <a id="10976" class="Symbol">:</a> <a id="10978" href="simple_essence.html#9583" class="Record">VectorSpace</a> <a id="10990" href="simple_essence.html#10869" class="Bound">T</a> <a id="10992" href="simple_essence.html#10882" class="Bound">A</a> <a id="10994" class="Symbol">⦄</a>
         <a id="11005" class="Comment">--------------------------------------</a>
      <a id="11050" class="Symbol">→</a> <a id="11052" href="simple_essence.html#10869" class="Bound">T</a> <a id="11054" class="Symbol">→</a> <a id="11056" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="11063" href="simple_essence.html#10869" class="Bound">T</a> <a id="11065" href="simple_essence.html#10882" class="Bound">A</a> <a id="11067" class="Symbol">{</a><a id="11068" href="simple_essence.html#10882" class="Bound">A</a><a id="11069" class="Symbol">}</a>
<a id="11071" href="simple_essence.html#10860" class="Function">a⊸§←a</a> <a id="11077" class="Symbol">=</a> <a id="11079" class="Symbol">λ</a> <a id="11081" class="Symbol">{</a> <a id="11083" href="simple_essence.html#11083" class="Bound">a</a> <a id="11085" class="Symbol">→</a> <a id="11087" href="simple_essence.html#8033" class="InductiveConstructor">mkLM</a> <a id="11092" class="Symbol">(</a><a id="11093" href="simple_essence.html#11083" class="Bound">a</a> <a id="11095" href="simple_essence.html#9798" class="Field Operator">⊙_</a><a id="11097" class="Symbol">)</a> <a id="11099" href="simple_essence.html#9876" class="Field">⊙-distrib-+</a> <a id="11111" href="simple_essence.html#10007" class="Field">⊙-comm-·</a> <a id="11120" class="Symbol">}</a>

<a id="11123" class="Comment">-- Danger, Will Robinson!</a>
<a id="11149" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="11161" href="simple_essence.html#11161" class="Postulate">x·z≡y·z→x≡y</a> <a id="11173" class="Symbol">:</a> <a id="11175" class="Symbol">{</a><a id="11176" href="simple_essence.html#11176" class="Bound">T</a> <a id="11178" class="Symbol">:</a> <a id="11180" class="PrimitiveType">Set</a> <a id="11184" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11186" class="Symbol">}</a> <a id="11188" class="Symbol">{</a><a id="11189" href="simple_essence.html#11189" class="Bound">A</a> <a id="11191" class="Symbol">:</a> <a id="11193" class="PrimitiveType">Set</a> <a id="11197" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11199" class="Symbol">}</a>
                 <a id="11218" class="Symbol">⦃</a> <a id="11220" href="simple_essence.html#11220" class="Bound">_</a> <a id="11222" class="Symbol">:</a> <a id="11224" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11229" href="simple_essence.html#11176" class="Bound">T</a> <a id="11231" class="Symbol">⦄</a> <a id="11233" class="Symbol">⦃</a> <a id="11235" href="simple_essence.html#11235" class="Bound">_</a> <a id="11237" class="Symbol">:</a> <a id="11239" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11244" href="simple_essence.html#11189" class="Bound">A</a> <a id="11246" class="Symbol">⦄</a>
                 <a id="11265" class="Symbol">⦃</a> <a id="11267" href="simple_essence.html#11267" class="Bound">_</a> <a id="11269" class="Symbol">:</a> <a id="11271" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="11280" href="simple_essence.html#11176" class="Bound">T</a> <a id="11282" href="simple_essence.html#11189" class="Bound">A</a> <a id="11284" class="Symbol">⦄</a> <a id="11286" class="Symbol">⦃</a> <a id="11288" href="simple_essence.html#11288" class="Bound">_</a> <a id="11290" class="Symbol">:</a> <a id="11292" href="simple_essence.html#9583" class="Record">VectorSpace</a> <a id="11304" href="simple_essence.html#11176" class="Bound">T</a> <a id="11306" href="simple_essence.html#11189" class="Bound">A</a> <a id="11308" class="Symbol">⦄</a>
                 <a id="11327" class="Symbol">{</a><a id="11328" href="simple_essence.html#11328" class="Bound">x</a> <a id="11330" href="simple_essence.html#11330" class="Bound">y</a> <a id="11332" class="Symbol">:</a> <a id="11334" href="simple_essence.html#11176" class="Bound">T</a><a id="11335" class="Symbol">}</a>
              <a id="11351" class="Symbol">→</a> <a id="11353" class="Symbol">(∀</a> <a id="11356" class="Symbol">{</a><a id="11357" href="simple_essence.html#11357" class="Bound">z</a> <a id="11359" class="Symbol">:</a> <a id="11361" href="simple_essence.html#11176" class="Bound">T</a><a id="11362" class="Symbol">}</a> <a id="11364" class="Symbol">→</a> <a id="11366" href="simple_essence.html#11328" class="Bound">x</a> <a id="11368" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="11370" href="simple_essence.html#11357" class="Bound">z</a> <a id="11372" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11374" href="simple_essence.html#11330" class="Bound">y</a> <a id="11376" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="11378" href="simple_essence.html#11357" class="Bound">z</a><a id="11379" class="Symbol">)</a>
                 <a id="11398" class="Comment">---------------------------------------------</a>
              <a id="11458" class="Symbol">→</a> <a id="11460" href="simple_essence.html#11328" class="Bound">x</a> <a id="11462" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11464" href="simple_essence.html#11330" class="Bound">y</a>
<a id="11466" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="11526" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="11593" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="11624" href="simple_essence.html#11624" class="Function">a⊸§↔a</a> <a id="11630" class="Symbol">:</a> <a id="11632" class="Symbol">{</a><a id="11633" href="simple_essence.html#11633" class="Bound">T</a> <a id="11635" class="Symbol">:</a> <a id="11637" class="PrimitiveType">Set</a> <a id="11641" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11643" class="Symbol">}</a> <a id="11645" class="Symbol">{</a><a id="11646" href="simple_essence.html#11646" class="Bound">A</a> <a id="11648" class="Symbol">:</a> <a id="11650" class="PrimitiveType">Set</a> <a id="11654" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11656" class="Symbol">}</a>
         <a id="11667" class="Symbol">⦃</a> <a id="11669" href="simple_essence.html#11669" class="Bound">_</a> <a id="11671" class="Symbol">:</a> <a id="11673" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11678" href="simple_essence.html#11633" class="Bound">T</a> <a id="11680" class="Symbol">⦄</a> <a id="11682" class="Symbol">⦃</a> <a id="11684" href="simple_essence.html#11684" class="Bound">_</a> <a id="11686" class="Symbol">:</a> <a id="11688" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11693" href="simple_essence.html#11646" class="Bound">A</a> <a id="11695" class="Symbol">⦄</a>
         <a id="11706" class="Symbol">⦃</a> <a id="11708" href="simple_essence.html#11708" class="Bound">_</a> <a id="11710" class="Symbol">:</a> <a id="11712" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="11721" href="simple_essence.html#11633" class="Bound">T</a> <a id="11723" href="simple_essence.html#11646" class="Bound">A</a> <a id="11725" class="Symbol">⦄</a> <a id="11727" class="Symbol">⦃</a> <a id="11729" href="simple_essence.html#11729" class="Bound">_</a> <a id="11731" class="Symbol">:</a> <a id="11733" href="simple_essence.html#9583" class="Record">VectorSpace</a> <a id="11745" href="simple_essence.html#11633" class="Bound">T</a> <a id="11747" href="simple_essence.html#11646" class="Bound">A</a> <a id="11749" class="Symbol">⦄</a>
         <a id="11760" class="Comment">---------------------------------------------</a>
      <a id="11812" class="Symbol">→</a> <a id="11814" class="Symbol">(</a><a id="11815" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="11822" href="simple_essence.html#11633" class="Bound">T</a> <a id="11824" href="simple_essence.html#11646" class="Bound">A</a><a id="11825" class="Symbol">)</a> <a id="11827" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="11829" href="simple_essence.html#11633" class="Bound">T</a>
<a id="11831" href="simple_essence.html#11624" class="Function">a⊸§↔a</a> <a id="11837" class="Symbol">=</a>
  <a id="11841" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="11845" class="Symbol">{</a><a id="11846" class="Argument">f</a> <a id="11848" class="Symbol">=</a> <a id="11850" href="simple_essence.html#10561" class="Function">a⊸§→a</a><a id="11855" class="Symbol">}</a> <a id="11857" class="Symbol">{</a><a id="11858" class="Argument">f⁻¹</a> <a id="11862" class="Symbol">=</a> <a id="11864" href="simple_essence.html#10860" class="Function">a⊸§←a</a><a id="11869" class="Symbol">}</a>
      <a id="11877" class="Symbol">(</a> <a id="11879" class="Symbol">(λ</a> <a id="11882" class="Symbol">{</a><a id="11883" href="simple_essence.html#11883" class="Bound">x</a> <a id="11885" class="Symbol">→</a> <a id="11887" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="11911" href="simple_essence.html#10561" class="Function">a⊸§→a</a> <a id="11917" class="Symbol">(</a><a id="11918" href="simple_essence.html#10860" class="Function">a⊸§←a</a> <a id="11924" href="simple_essence.html#11883" class="Bound">x</a><a id="11925" class="Symbol">)</a>
                <a id="11943" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="11965" href="simple_essence.html#10561" class="Function">a⊸§→a</a> <a id="11971" class="Symbol">(</a><a id="11972" href="simple_essence.html#8033" class="InductiveConstructor">mkLM</a> <a id="11977" class="Symbol">(</a><a id="11978" href="simple_essence.html#11883" class="Bound">x</a> <a id="11980" href="simple_essence.html#9798" class="Field Operator">⊙_</a><a id="11982" class="Symbol">)</a> <a id="11984" href="simple_essence.html#9876" class="Field">⊙-distrib-+</a> <a id="11996" href="simple_essence.html#10007" class="Field">⊙-comm-·</a><a id="12004" class="Symbol">)</a>
                <a id="12022" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="12044" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12050" class="Symbol">(λ</a> <a id="12053" href="simple_essence.html#12053" class="Bound">acc</a> <a id="12057" href="simple_essence.html#12057" class="Bound">v</a> <a id="12059" class="Symbol">→</a> <a id="12061" href="simple_essence.html#12053" class="Bound">acc</a> <a id="12065" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="12067" class="Symbol">(</a><a id="12068" href="simple_essence.html#11883" class="Bound">x</a> <a id="12070" href="simple_essence.html#9798" class="Field Operator">⊙</a> <a id="12072" href="simple_essence.html#12057" class="Bound">v</a><a id="12073" class="Symbol">)</a> <a id="12075" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="12077" href="simple_essence.html#12057" class="Bound">v</a><a id="12078" class="Symbol">)</a> <a id="12080" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="12082" href="simple_essence.html#9773" class="Field">basisSet</a>
                <a id="12107" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12110" href="simple_essence.html#11161" class="Postulate">x·z≡y·z→x≡y</a> <a id="12122" href="simple_essence.html#10132" class="Field">orthonormal</a> <a id="12134" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="12154" href="simple_essence.html#11883" class="Bound">x</a>
                <a id="12172" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12173" class="Symbol">})</a>
      <a id="12182" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="12184" class="Symbol">λ</a> <a id="12186" class="Symbol">{</a><a id="12187" href="simple_essence.html#12187" class="Bound">lm</a> <a id="12190" class="Symbol">→</a> <a id="12192" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                    <a id="12218" href="simple_essence.html#10860" class="Function">a⊸§←a</a> <a id="12224" class="Symbol">(</a><a id="12225" href="simple_essence.html#10561" class="Function">a⊸§→a</a> <a id="12231" href="simple_essence.html#12187" class="Bound">lm</a><a id="12233" class="Symbol">)</a>
                  <a id="12253" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12277" href="simple_essence.html#10860" class="Function">a⊸§←a</a> <a id="12283" class="Symbol">(</a><a id="12284" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12290" class="Symbol">(λ</a> <a id="12293" href="simple_essence.html#12293" class="Bound">acc</a> <a id="12297" href="simple_essence.html#12297" class="Bound">v</a> <a id="12299" class="Symbol">→</a>
                                     <a id="12338" href="simple_essence.html#12293" class="Bound">acc</a> <a id="12342" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="12344" class="Symbol">(</a><a id="12345" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="12354" href="simple_essence.html#12187" class="Bound">lm</a> <a id="12357" href="simple_essence.html#12297" class="Bound">v</a><a id="12358" class="Symbol">)</a> <a id="12360" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="12362" href="simple_essence.html#12297" class="Bound">v</a><a id="12363" class="Symbol">)</a> <a id="12365" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="12367" href="simple_essence.html#9773" class="Field">basisSet</a><a id="12375" class="Symbol">)</a>
                  <a id="12395" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12419" href="simple_essence.html#8033" class="InductiveConstructor">mkLM</a> <a id="12424" class="Symbol">(</a> <a id="12426" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12432" class="Symbol">(</a> <a id="12434" class="Symbol">λ</a> <a id="12436" href="simple_essence.html#12436" class="Bound">acc</a> <a id="12440" href="simple_essence.html#12440" class="Bound">v</a> <a id="12442" class="Symbol">→</a>
                                     <a id="12481" href="simple_essence.html#12436" class="Bound">acc</a> <a id="12485" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="12487" class="Symbol">(</a><a id="12488" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="12497" href="simple_essence.html#12187" class="Bound">lm</a> <a id="12500" href="simple_essence.html#12440" class="Bound">v</a><a id="12501" class="Symbol">)</a> <a id="12503" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="12505" href="simple_essence.html#12440" class="Bound">v</a>
                                 <a id="12540" class="Symbol">)</a> <a id="12542" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="12544" href="simple_essence.html#9773" class="Field">basisSet</a>
                           <a id="12580" href="simple_essence.html#9798" class="Field Operator">⊙_</a>
                         <a id="12608" class="Symbol">)</a> <a id="12610" href="simple_essence.html#9876" class="Field">⊙-distrib-+</a> <a id="12622" href="simple_essence.html#10007" class="Field">⊙-comm-·</a>
                  <a id="12649" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12652" href="simple_essence.html#8372" class="Postulate">⊸≡</a> <a id="12655" class="Symbol">(</a> <a id="12657" href="simple_essence.html#6434" class="Postulate">extensionality</a>
                            <a id="12700" class="Symbol">(</a> <a id="12702" class="Symbol">λ</a> <a id="12704" href="simple_essence.html#12704" class="Bound">x</a> <a id="12706" class="Symbol">→</a> <a id="12708" href="simple_essence.html#10132" class="Field">orthonormal</a> <a id="12720" class="Symbol">{</a><a id="12721" class="Argument">f</a> <a id="12723" class="Symbol">=</a> <a id="12725" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="12734" href="simple_essence.html#12187" class="Bound">lm</a><a id="12736" class="Symbol">}</a> <a id="12738" class="Symbol">{</a><a id="12739" class="Argument">x</a> <a id="12741" class="Symbol">=</a> <a id="12743" href="simple_essence.html#12704" class="Bound">x</a><a id="12744" class="Symbol">}</a> <a id="12746" class="Symbol">)</a>
                        <a id="12772" class="Symbol">)</a>
                   <a id="12793" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                    <a id="12815" href="simple_essence.html#12187" class="Bound">lm</a>
                  <a id="12836" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12837" class="Symbol">}</a>
      <a id="12845" class="Symbol">)</a>

</pre>
### Stashed

Stashed coding attempts.

<pre class="Agda"><a id="12900" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="12983" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="13045" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="13139" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="13202" class="Comment">--</a>
<a id="13205" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="13228" class="Comment">--         ⦃_ : Additive A⦄ ⦃_ : Scalable A⦄</a>
<a id="13273" class="Comment">--         ⦃_ : VectorSpace A⦄</a>
<a id="13304" class="Comment">--         -------------------------------------</a>
<a id="13353" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="13381" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

<a id="13413" class="Comment">-- -- f(0) = 0</a>
<a id="13428" class="Comment">-- zero-lin : {A B : Set a}</a>
<a id="13456" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13507" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13558" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>

<a id="13591" class="Comment">-- -- Injectivity of linear function</a>
<a id="13628" class="Comment">-- inj-lin : {A B : Set a} {x y : A}</a>
<a id="13665" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13716" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13767" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>
<a id="13799" class="Comment">--        → LinMap.f _ x ≡ LinMap.f _ y</a>
<a id="13839" class="Comment">--           ---------------------------</a>
<a id="13880" class="Comment">--        → x ≡ y</a>
<a id="13898" class="Comment">-- inj-lin {x = x} {y = y} fx≡fy =</a>
<a id="13933" class="Comment">--   let f = LinMap.f _</a>
<a id="13957" class="Comment">--    in begin</a>
<a id="13972" class="Comment">--         x</a>
<a id="13985" class="Comment">--       ≡⟨⟩</a>
<a id="13998" class="Comment">--         f (x - y)</a>
<a id="14019" class="Comment">--       ≡⟨ LinMap.adds _ ⟩</a>
<a id="14047" class="Comment">--         f x - f y</a>
<a id="14068" class="Comment">--       ≡⟨ sub-≡ fx≡fy ⟩</a>
<a id="14094" class="Comment">--         0</a>
<a id="14107" class="Comment">--       ≡⟨⟩</a>
<a id="14120" class="Comment">--         y</a>
<a id="14133" class="Comment">--       ∎</a>
      
<a id="14151" class="Comment">-- cong-app′ : ∀ {A : Set a} {B : Set b} {f : A → B} {x y : A}</a>
<a id="14214" class="Comment">--          → f x ≡ f y</a>
<a id="14238" class="Comment">--             ---------</a>
<a id="14263" class="Comment">--          → x ≡ y</a>
<a id="14283" class="Comment">-- cong-app′ fx≡fy = {!contraposition!}</a>
         
<a id="14333" class="Comment">-- x·z≡y·z→x≡y : {A : Set a}</a>
<a id="14362" class="Comment">--                ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="14418" class="Comment">--                ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="14477" class="Comment">--                {x y : A}</a>
<a id="14505" class="Comment">--             → (∀ {z : A} → x · z ≡ y · z)</a>
<a id="14550" class="Comment">--                ------------------------------------------------------------</a>
<a id="14629" class="Comment">--             → x ≡ y</a>
<a id="14652" class="Comment">-- x·z≡y·z→x≡y {x = x} {y = y} g =</a>
<a id="14687" class="Comment">--   let f = LinMap.f _</a>
<a id="14711" class="Comment">--       z = foldl (λ acc v → acc ⊕ f v ⊛ v) id⊕ basisSet</a>
<a id="14769" class="Comment">--       x·z≡y·z = g {z}</a>
<a id="14794" class="Comment">--    in cong-app refl {!!}</a>
<a id="14822" class="Comment">--    -- in begin</a>
<a id="14840" class="Comment">--    --      -- ?</a>
<a id="14859" class="Comment">--    --      x·z≡y·z</a>
<a id="14881" class="Comment">--    --    -- ≡⟨ ? ⟩</a>
<a id="14903" class="Comment">--    --    --   x · z ≡ y · z</a>
<a id="14934" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="14953" class="Comment">--    --    -- ≡⟨ cong (_≡ y · z) comm-· ⟩</a>
<a id="14996" class="Comment">--    --      z · x ≡ y · z</a>
<a id="15024" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15043" class="Comment">--    --    -- ≡⟨ cong (z · x ≡_) comm-· ⟩</a>
<a id="15086" class="Comment">--    --      z · x ≡ z · y</a>
<a id="15114" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15133" class="Comment">--    --    -- ≡⟨ cong (_≡ z · y) (orthonormal) ⟩</a>
<a id="15183" class="Comment">--    --      f x ≡ z · y</a>
<a id="15209" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15228" class="Comment">--    --    -- ≡⟨ cong (f x ≡_) (orthonormal) ⟩</a>
<a id="15276" class="Comment">--    --      f x ≡ f y</a>
<a id="15300" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15319" class="Comment">--    --    -- ≡⟨ cong-app ⟩</a>
<a id="15348" class="Comment">--    --      x ≡ y</a>
<a id="15368" class="Comment">--    --    ∎</a>

<a id="15383" class="Comment">-- -- So, how was Agsy able to jump over all of that?</a>
<a id="15437" class="Comment">-- -- My usual experience w/ Agsy is that when I ask it to solve anything</a>
<a id="15511" class="Comment">-- -- non-trivial by itself it always complains, &quot;Sorry, I don&#39;t support</a>
<a id="15584" class="Comment">-- -- literals, yet.&quot;, which I&#39;ve never understood.</a>

<a id="15637" class="Comment">-- a⊸§↔a : {A : Set a}</a>
<a id="15660" class="Comment">--          ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="15710" class="Comment">--          ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="15763" class="Comment">--          -----------------------------------------</a>
<a id="15817" class="Comment">--       → (LinMap A §) ↔ A</a>
<a id="15845" class="Comment">-- a⊸§↔a {A} =</a>
<a id="15860" class="Comment">--   mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}</a>
<a id="15895" class="Comment">--       ( (λ {x → begin</a>
<a id="15920" class="Comment">--                   a⊸§→a (a⊸§←a x)</a>
<a id="15957" class="Comment">--                 ≡⟨⟩</a>
<a id="15980" class="Comment">--                   a⊸§→a (mkLM (x ·_) ·-distrib-⊕ ·-comm-⊛)</a>
<a id="16042" class="Comment">--                 ≡⟨⟩</a>
<a id="16065" class="Comment">--                   foldl (λ acc v → acc ⊕ (x · v) ⊛ v) id⊕ basisSet</a>
<a id="16135" class="Comment">--                 ≡⟨ x·z≡y·z→x≡y (orthonormal {f = (x ·_)}) ⟩</a>
<a id="16198" class="Comment">--                   x</a>
<a id="16221" class="Comment">--                 ∎})</a>
<a id="16244" class="Comment">--       , λ {lm → begin</a>
<a id="16269" class="Comment">--                   a⊸§←a (a⊸§→a lm)</a>
<a id="16307" class="Comment">--                 ≡⟨⟩</a>
<a id="16330" class="Comment">--                   a⊸§←a (foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)</a>
<a id="16416" class="Comment">--                 ≡⟨⟩</a>
<a id="16439" class="Comment">--                   mkLM ((foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)·_)</a>
<a id="16528" class="Comment">--                        ·-distrib-⊕ ·-comm-⊛</a>
<a id="16575" class="Comment">--                 ≡⟨ ⊸≡ ( extensionality</a>
<a id="16617" class="Comment">--                           ( λ x → orthonormal {f = LinMap.f lm} {x = x} )</a>
<a id="16694" class="Comment">--                       )</a>
<a id="16721" class="Comment">--                  ⟩</a>
<a id="16743" class="Comment">--                   lm</a>
<a id="16767" class="Comment">--                 ∎}</a>
<a id="16789" class="Comment">--       )</a>


</pre>