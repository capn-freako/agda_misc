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
:   We can "add" two vectors, producing a third.

Scalar Multiplication
:   We can "scale" a vector by an element of the carrier type, producing another vector.

Inner Product
:   We can combine two vectors, producing a single value of the carrier type.

**Note:** The remaining definitions in the code below were the result of attempting to solve the first isomorphism.

**Note:** We use `Ring`, as opposed to a `SemiRing`, because that gives us _subtraction_, which allows us to prove _injectivity_ of linear maps, which in turn allows us to replace the `x·z≡y·z→x≡y` _postulate_ with an equivalent _proof_.

<pre class="Agda"><a id="9570" class="Keyword">record</a> <a id="VectorSpace"></a><a id="9577" href="simple_essence.html#9577" class="Record">VectorSpace</a>
  <a id="9591" class="Symbol">(</a><a id="9592" href="simple_essence.html#9592" class="Bound">T</a> <a id="9594" class="Symbol">:</a> <a id="9596" class="PrimitiveType">Set</a> <a id="9600" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="9602" class="Symbol">)</a> <a id="9604" class="Symbol">(</a><a id="9605" href="simple_essence.html#9605" class="Bound">A</a> <a id="9607" class="Symbol">:</a> <a id="9609" class="PrimitiveType">Set</a> <a id="9613" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="9615" class="Symbol">)</a>
  <a id="9619" class="Symbol">⦃</a> <a id="9621" href="simple_essence.html#9621" class="Bound">_</a> <a id="9623" class="Symbol">:</a> <a id="9625" href="simple_essence.html#7186" class="Record">Ring</a> <a id="9630" href="simple_essence.html#9592" class="Bound">T</a> <a id="9632" class="Symbol">⦄</a> <a id="9634" class="Symbol">⦃</a> <a id="9636" href="simple_essence.html#9636" class="Bound">_</a> <a id="9638" class="Symbol">:</a> <a id="9640" href="simple_essence.html#7186" class="Record">Ring</a> <a id="9645" href="simple_essence.html#9605" class="Bound">A</a> <a id="9647" class="Symbol">⦄</a> <a id="9649" class="Symbol">⦃</a> <a id="9651" href="simple_essence.html#9651" class="Bound">_</a> <a id="9653" class="Symbol">:</a> <a id="9655" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="9664" href="simple_essence.html#9592" class="Bound">T</a> <a id="9666" href="simple_essence.html#9605" class="Bound">A</a> <a id="9668" class="Symbol">⦄</a>
  <a id="9672" class="Symbol">:</a> <a id="9674" class="PrimitiveType">Set</a> <a id="9678" class="Symbol">(</a><a id="9679" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="9689" href="simple_essence.html#9600" class="Bound">ℓ₁</a><a id="9691" class="Symbol">)</a> <a id="9693" class="Keyword">where</a>
  <a id="9701" class="Keyword">infix</a>  <a id="9708" class="Number">7</a> <a id="9710" href="simple_essence.html#9792" class="Field Operator">_⊙_</a>
  <a id="9716" class="Keyword">field</a>
    <a id="VectorSpace.I"></a><a id="9726" href="simple_essence.html#9726" class="Field">I</a>     <a id="9732" class="Symbol">:</a> <a id="9734" class="PrimitiveType">Set</a> <a id="9738" href="simple_essence.html#9600" class="Bound">ℓ₁</a>
    <a id="VectorSpace.index"></a><a id="9745" href="simple_essence.html#9745" class="Field">index</a> <a id="9751" class="Symbol">:</a> <a id="9753" href="simple_essence.html#9726" class="Field">I</a> <a id="9755" class="Symbol">→</a> <a id="9757" href="simple_essence.html#9592" class="Bound">T</a> <a id="9759" class="Symbol">→</a> <a id="9761" href="simple_essence.html#9605" class="Bound">A</a>
    <a id="VectorSpace.basisSet"></a><a id="9767" href="simple_essence.html#9767" class="Field">basisSet</a>    <a id="9779" class="Symbol">:</a> <a id="9781" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="9786" href="simple_essence.html#9592" class="Bound">T</a>
    <a id="VectorSpace._⊙_"></a><a id="9792" href="simple_essence.html#9792" class="Field Operator">_⊙_</a>         <a id="9804" class="Symbol">:</a> <a id="9806" href="simple_essence.html#9592" class="Bound">T</a> <a id="9808" class="Symbol">→</a> <a id="9810" href="simple_essence.html#9592" class="Bound">T</a> <a id="9812" class="Symbol">→</a> <a id="9814" href="simple_essence.html#9605" class="Bound">A</a>
    <a id="9820" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.⊙-distrib-+"></a><a id="9870" href="simple_essence.html#9870" class="Field">⊙-distrib-+</a> <a id="9882" class="Symbol">:</a> <a id="9884" class="Symbol">∀</a> <a id="9886" class="Symbol">{</a><a id="9887" href="simple_essence.html#9887" class="Bound">a</a> <a id="9889" href="simple_essence.html#9889" class="Bound">b</a> <a id="9891" href="simple_essence.html#9891" class="Bound">c</a> <a id="9893" class="Symbol">:</a> <a id="9895" href="simple_essence.html#9592" class="Bound">T</a><a id="9896" class="Symbol">}</a>
                  <a id="9916" class="Comment">-------------------------------</a>
               <a id="9963" class="Symbol">→</a> <a id="9965" href="simple_essence.html#9887" class="Bound">a</a> <a id="9967" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="9969" class="Symbol">(</a><a id="9970" href="simple_essence.html#9889" class="Bound">b</a> <a id="9972" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="9974" href="simple_essence.html#9891" class="Bound">c</a><a id="9975" class="Symbol">)</a> <a id="9977" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9979" class="Symbol">(</a><a id="9980" href="simple_essence.html#9887" class="Bound">a</a> <a id="9982" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="9984" href="simple_essence.html#9889" class="Bound">b</a><a id="9985" class="Symbol">)</a> <a id="9987" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="9989" class="Symbol">(</a><a id="9990" href="simple_essence.html#9887" class="Bound">a</a> <a id="9992" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="9994" href="simple_essence.html#9891" class="Bound">c</a><a id="9995" class="Symbol">)</a>
    <a id="VectorSpace.⊙-comm-·"></a><a id="10001" href="simple_essence.html#10001" class="Field">⊙-comm-·</a>    <a id="10013" class="Symbol">:</a> <a id="10015" class="Symbol">∀</a> <a id="10017" class="Symbol">{</a><a id="10018" href="simple_essence.html#10018" class="Bound">s</a> <a id="10020" class="Symbol">:</a> <a id="10022" href="simple_essence.html#9605" class="Bound">A</a><a id="10023" class="Symbol">}</a> <a id="10025" class="Symbol">{</a><a id="10026" href="simple_essence.html#10026" class="Bound">a</a> <a id="10028" href="simple_essence.html#10028" class="Bound">b</a> <a id="10030" class="Symbol">:</a> <a id="10032" href="simple_essence.html#9592" class="Bound">T</a><a id="10033" class="Symbol">}</a>
                  <a id="10053" class="Comment">-------------------------</a>
               <a id="10094" class="Symbol">→</a> <a id="10096" href="simple_essence.html#10026" class="Bound">a</a> <a id="10098" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="10100" class="Symbol">(</a><a id="10101" href="simple_essence.html#10018" class="Bound">s</a> <a id="10103" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10105" href="simple_essence.html#10028" class="Bound">b</a><a id="10106" class="Symbol">)</a> <a id="10108" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10110" href="simple_essence.html#10018" class="Bound">s</a> <a id="10112" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10114" class="Symbol">(</a><a id="10115" href="simple_essence.html#10026" class="Bound">a</a> <a id="10117" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="10119" href="simple_essence.html#10028" class="Bound">b</a><a id="10120" class="Symbol">)</a>
    <a id="VectorSpace.orthonormal"></a><a id="10126" href="simple_essence.html#10126" class="Field">orthonormal</a> <a id="10138" class="Symbol">:</a> <a id="10140" class="Symbol">∀</a> <a id="10142" class="Symbol">{</a><a id="10143" href="simple_essence.html#10143" class="Bound">f</a> <a id="10145" class="Symbol">:</a> <a id="10147" href="simple_essence.html#9592" class="Bound">T</a> <a id="10149" class="Symbol">→</a> <a id="10151" href="simple_essence.html#9605" class="Bound">A</a><a id="10152" class="Symbol">}</a>
               <a id="10169" class="Symbol">→</a> <a id="10171" class="Symbol">{</a><a id="10172" href="simple_essence.html#10172" class="Bound">x</a> <a id="10174" class="Symbol">:</a> <a id="10176" href="simple_essence.html#9592" class="Bound">T</a><a id="10177" class="Symbol">}</a>
                  <a id="10197" class="Comment">------------------------------------</a>
               <a id="10249" class="Symbol">→</a> <a id="10251" class="Symbol">(</a> <a id="10253" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10259" class="Symbol">(λ</a> <a id="10262" href="simple_essence.html#10262" class="Bound">acc</a> <a id="10266" href="simple_essence.html#10266" class="Bound">v</a> <a id="10268" class="Symbol">→</a> <a id="10270" href="simple_essence.html#10262" class="Bound">acc</a> <a id="10274" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="10276" class="Symbol">(</a><a id="10277" href="simple_essence.html#10143" class="Bound">f</a> <a id="10279" href="simple_essence.html#10266" class="Bound">v</a><a id="10280" class="Symbol">)</a> <a id="10282" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10284" href="simple_essence.html#10266" class="Bound">v</a><a id="10285" class="Symbol">)</a>
                          <a id="10313" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="10315" href="simple_essence.html#9767" class="Field">basisSet</a>
                  <a id="10342" class="Symbol">)</a> <a id="10344" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="10346" href="simple_essence.html#10172" class="Bound">x</a> <a id="10348" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10350" href="simple_essence.html#10143" class="Bound">f</a> <a id="10352" href="simple_essence.html#10172" class="Bound">x</a>
<a id="10354" class="Keyword">open</a> <a id="10359" href="simple_essence.html#9577" class="Module">VectorSpace</a> <a id="10371" class="Symbol">⦃</a> <a id="10373" class="Symbol">...</a> <a id="10377" class="Symbol">⦄</a> <a id="10379" class="Keyword">public</a>

</pre>
### Isomorphism 1: `(A ⊸ s) ↔ A`

Here, I prove that a linear map from some "vector" type `T` to a scalar of its _carrier_ type `A` is isomorphic to `T`.

<pre class="Agda"><a id="a⊸§→a"></a><a id="10555" href="simple_essence.html#10555" class="Function">a⊸§→a</a> <a id="10561" class="Symbol">:</a> <a id="10563" class="Symbol">{</a><a id="10564" href="simple_essence.html#10564" class="Bound">T</a> <a id="10566" class="Symbol">:</a> <a id="10568" class="PrimitiveType">Set</a> <a id="10572" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10574" class="Symbol">}</a> <a id="10576" class="Symbol">{</a><a id="10577" href="simple_essence.html#10577" class="Bound">A</a> <a id="10579" class="Symbol">:</a> <a id="10581" class="PrimitiveType">Set</a> <a id="10585" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10587" class="Symbol">}</a>
         <a id="10598" class="Symbol">⦃</a> <a id="10600" href="simple_essence.html#10600" class="Bound">_</a> <a id="10602" class="Symbol">:</a> <a id="10604" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10609" href="simple_essence.html#10564" class="Bound">T</a> <a id="10611" class="Symbol">⦄</a> <a id="10613" class="Symbol">⦃</a> <a id="10615" href="simple_essence.html#10615" class="Bound">_</a> <a id="10617" class="Symbol">:</a> <a id="10619" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10624" href="simple_essence.html#10577" class="Bound">A</a> <a id="10626" class="Symbol">⦄</a>
         <a id="10637" class="Symbol">⦃</a> <a id="10639" href="simple_essence.html#10639" class="Bound">_</a> <a id="10641" class="Symbol">:</a> <a id="10643" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="10652" href="simple_essence.html#10564" class="Bound">T</a> <a id="10654" href="simple_essence.html#10577" class="Bound">A</a> <a id="10656" class="Symbol">⦄</a>
         <a id="10667" class="Symbol">⦃</a> <a id="10669" href="simple_essence.html#10669" class="Bound">_</a> <a id="10671" class="Symbol">:</a> <a id="10673" href="simple_essence.html#9577" class="Record">VectorSpace</a> <a id="10685" href="simple_essence.html#10564" class="Bound">T</a> <a id="10687" href="simple_essence.html#10577" class="Bound">A</a> <a id="10689" class="Symbol">⦄</a>
         <a id="10700" class="Comment">------------------------------</a>
      <a id="10737" class="Symbol">→</a> <a id="10739" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="10746" href="simple_essence.html#10564" class="Bound">T</a> <a id="10748" href="simple_essence.html#10577" class="Bound">A</a> <a id="10750" class="Symbol">{</a><a id="10751" href="simple_essence.html#10577" class="Bound">A</a><a id="10752" class="Symbol">}</a> <a id="10754" class="Symbol">→</a> <a id="10756" href="simple_essence.html#10564" class="Bound">T</a>
<a id="10758" href="simple_essence.html#10555" class="Function">a⊸§→a</a> <a id="10764" class="Symbol">=</a> <a id="10766" class="Symbol">λ</a> <a id="10768" class="Symbol">{</a> <a id="10770" href="simple_essence.html#10770" class="Bound">lm</a> <a id="10773" class="Symbol">→</a> <a id="10775" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10781" class="Symbol">(λ</a> <a id="10784" href="simple_essence.html#10784" class="Bound">acc</a> <a id="10788" href="simple_essence.html#10788" class="Bound">v</a> <a id="10790" class="Symbol">→</a>
                     <a id="10813" href="simple_essence.html#10784" class="Bound">acc</a> <a id="10817" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="10819" class="Symbol">(</a><a id="10820" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="10829" href="simple_essence.html#10770" class="Bound">lm</a> <a id="10832" href="simple_essence.html#10788" class="Bound">v</a><a id="10833" class="Symbol">)</a> <a id="10835" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="10837" href="simple_essence.html#10788" class="Bound">v</a><a id="10838" class="Symbol">)</a> <a id="10840" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="10842" href="simple_essence.html#9767" class="Field">basisSet</a> <a id="10851" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="10854" href="simple_essence.html#10854" class="Function">a⊸§←a</a> <a id="10860" class="Symbol">:</a> <a id="10862" class="Symbol">{</a><a id="10863" href="simple_essence.html#10863" class="Bound">T</a> <a id="10865" class="Symbol">:</a> <a id="10867" class="PrimitiveType">Set</a> <a id="10871" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10873" class="Symbol">}</a> <a id="10875" class="Symbol">{</a><a id="10876" href="simple_essence.html#10876" class="Bound">A</a> <a id="10878" class="Symbol">:</a> <a id="10880" class="PrimitiveType">Set</a> <a id="10884" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="10886" class="Symbol">}</a>
         <a id="10897" class="Symbol">⦃</a> <a id="10899" href="simple_essence.html#10899" class="Bound">_</a> <a id="10901" class="Symbol">:</a> <a id="10903" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10908" href="simple_essence.html#10863" class="Bound">T</a> <a id="10910" class="Symbol">⦄</a> <a id="10912" class="Symbol">⦃</a> <a id="10914" href="simple_essence.html#10914" class="Bound">_</a> <a id="10916" class="Symbol">:</a> <a id="10918" href="simple_essence.html#7186" class="Record">Ring</a> <a id="10923" href="simple_essence.html#10876" class="Bound">A</a> <a id="10925" class="Symbol">⦄</a>
         <a id="10936" class="Symbol">⦃</a> <a id="10938" href="simple_essence.html#10938" class="Bound">_</a> <a id="10940" class="Symbol">:</a> <a id="10942" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="10951" href="simple_essence.html#10863" class="Bound">T</a> <a id="10953" href="simple_essence.html#10876" class="Bound">A</a> <a id="10955" class="Symbol">⦄</a>
         <a id="10966" class="Symbol">⦃</a> <a id="10968" href="simple_essence.html#10968" class="Bound">_</a> <a id="10970" class="Symbol">:</a> <a id="10972" href="simple_essence.html#9577" class="Record">VectorSpace</a> <a id="10984" href="simple_essence.html#10863" class="Bound">T</a> <a id="10986" href="simple_essence.html#10876" class="Bound">A</a> <a id="10988" class="Symbol">⦄</a>
         <a id="10999" class="Comment">--------------------------------------</a>
      <a id="11044" class="Symbol">→</a> <a id="11046" href="simple_essence.html#10863" class="Bound">T</a> <a id="11048" class="Symbol">→</a> <a id="11050" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="11057" href="simple_essence.html#10863" class="Bound">T</a> <a id="11059" href="simple_essence.html#10876" class="Bound">A</a> <a id="11061" class="Symbol">{</a><a id="11062" href="simple_essence.html#10876" class="Bound">A</a><a id="11063" class="Symbol">}</a>
<a id="11065" href="simple_essence.html#10854" class="Function">a⊸§←a</a> <a id="11071" class="Symbol">=</a> <a id="11073" class="Symbol">λ</a> <a id="11075" class="Symbol">{</a> <a id="11077" href="simple_essence.html#11077" class="Bound">a</a> <a id="11079" class="Symbol">→</a> <a id="11081" href="simple_essence.html#8033" class="InductiveConstructor">mkLM</a> <a id="11086" class="Symbol">(</a><a id="11087" href="simple_essence.html#11077" class="Bound">a</a> <a id="11089" href="simple_essence.html#9792" class="Field Operator">⊙_</a><a id="11091" class="Symbol">)</a> <a id="11093" href="simple_essence.html#9870" class="Field">⊙-distrib-+</a> <a id="11105" href="simple_essence.html#10001" class="Field">⊙-comm-·</a> <a id="11114" class="Symbol">}</a>

<a id="11117" class="Comment">-- Danger, Will Robinson!</a>
<a id="11143" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="11155" href="simple_essence.html#11155" class="Postulate">x·z≡y·z→x≡y</a> <a id="11167" class="Symbol">:</a> <a id="11169" class="Symbol">{</a><a id="11170" href="simple_essence.html#11170" class="Bound">T</a> <a id="11172" class="Symbol">:</a> <a id="11174" class="PrimitiveType">Set</a> <a id="11178" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11180" class="Symbol">}</a> <a id="11182" class="Symbol">{</a><a id="11183" href="simple_essence.html#11183" class="Bound">A</a> <a id="11185" class="Symbol">:</a> <a id="11187" class="PrimitiveType">Set</a> <a id="11191" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11193" class="Symbol">}</a>
                 <a id="11212" class="Symbol">⦃</a> <a id="11214" href="simple_essence.html#11214" class="Bound">_</a> <a id="11216" class="Symbol">:</a> <a id="11218" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11223" href="simple_essence.html#11170" class="Bound">T</a> <a id="11225" class="Symbol">⦄</a> <a id="11227" class="Symbol">⦃</a> <a id="11229" href="simple_essence.html#11229" class="Bound">_</a> <a id="11231" class="Symbol">:</a> <a id="11233" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11238" href="simple_essence.html#11183" class="Bound">A</a> <a id="11240" class="Symbol">⦄</a>
                 <a id="11259" class="Symbol">⦃</a> <a id="11261" href="simple_essence.html#11261" class="Bound">_</a> <a id="11263" class="Symbol">:</a> <a id="11265" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="11274" href="simple_essence.html#11170" class="Bound">T</a> <a id="11276" href="simple_essence.html#11183" class="Bound">A</a> <a id="11278" class="Symbol">⦄</a> <a id="11280" class="Symbol">⦃</a> <a id="11282" href="simple_essence.html#11282" class="Bound">_</a> <a id="11284" class="Symbol">:</a> <a id="11286" href="simple_essence.html#9577" class="Record">VectorSpace</a> <a id="11298" href="simple_essence.html#11170" class="Bound">T</a> <a id="11300" href="simple_essence.html#11183" class="Bound">A</a> <a id="11302" class="Symbol">⦄</a>
                 <a id="11321" class="Symbol">{</a><a id="11322" href="simple_essence.html#11322" class="Bound">x</a> <a id="11324" href="simple_essence.html#11324" class="Bound">y</a> <a id="11326" class="Symbol">:</a> <a id="11328" href="simple_essence.html#11170" class="Bound">T</a><a id="11329" class="Symbol">}</a>
              <a id="11345" class="Symbol">→</a> <a id="11347" class="Symbol">(∀</a> <a id="11350" class="Symbol">{</a><a id="11351" href="simple_essence.html#11351" class="Bound">z</a> <a id="11353" class="Symbol">:</a> <a id="11355" href="simple_essence.html#11170" class="Bound">T</a><a id="11356" class="Symbol">}</a> <a id="11358" class="Symbol">→</a> <a id="11360" href="simple_essence.html#11322" class="Bound">x</a> <a id="11362" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="11364" href="simple_essence.html#11351" class="Bound">z</a> <a id="11366" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11368" href="simple_essence.html#11324" class="Bound">y</a> <a id="11370" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="11372" href="simple_essence.html#11351" class="Bound">z</a><a id="11373" class="Symbol">)</a>
                 <a id="11392" class="Comment">---------------------------------------------</a>
              <a id="11452" class="Symbol">→</a> <a id="11454" href="simple_essence.html#11322" class="Bound">x</a> <a id="11456" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11458" href="simple_essence.html#11324" class="Bound">y</a>
<a id="11460" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="11520" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="11587" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="11618" href="simple_essence.html#11618" class="Function">a⊸§↔a</a> <a id="11624" class="Symbol">:</a> <a id="11626" class="Symbol">{</a><a id="11627" href="simple_essence.html#11627" class="Bound">T</a> <a id="11629" class="Symbol">:</a> <a id="11631" class="PrimitiveType">Set</a> <a id="11635" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11637" class="Symbol">}</a> <a id="11639" class="Symbol">{</a><a id="11640" href="simple_essence.html#11640" class="Bound">A</a> <a id="11642" class="Symbol">:</a> <a id="11644" class="PrimitiveType">Set</a> <a id="11648" href="simple_essence.html#6402" class="Generalizable">ℓ₁</a><a id="11650" class="Symbol">}</a>
         <a id="11661" class="Symbol">⦃</a> <a id="11663" href="simple_essence.html#11663" class="Bound">_</a> <a id="11665" class="Symbol">:</a> <a id="11667" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11672" href="simple_essence.html#11627" class="Bound">T</a> <a id="11674" class="Symbol">⦄</a> <a id="11676" class="Symbol">⦃</a> <a id="11678" href="simple_essence.html#11678" class="Bound">_</a> <a id="11680" class="Symbol">:</a> <a id="11682" href="simple_essence.html#7186" class="Record">Ring</a> <a id="11687" href="simple_essence.html#11640" class="Bound">A</a> <a id="11689" class="Symbol">⦄</a>
         <a id="11700" class="Symbol">⦃</a> <a id="11702" href="simple_essence.html#11702" class="Bound">_</a> <a id="11704" class="Symbol">:</a> <a id="11706" href="simple_essence.html#7045" class="Record">Scalable</a> <a id="11715" href="simple_essence.html#11627" class="Bound">T</a> <a id="11717" href="simple_essence.html#11640" class="Bound">A</a> <a id="11719" class="Symbol">⦄</a> <a id="11721" class="Symbol">⦃</a> <a id="11723" href="simple_essence.html#11723" class="Bound">_</a> <a id="11725" class="Symbol">:</a> <a id="11727" href="simple_essence.html#9577" class="Record">VectorSpace</a> <a id="11739" href="simple_essence.html#11627" class="Bound">T</a> <a id="11741" href="simple_essence.html#11640" class="Bound">A</a> <a id="11743" class="Symbol">⦄</a>
         <a id="11754" class="Comment">---------------------------------------------</a>
      <a id="11806" class="Symbol">→</a> <a id="11808" class="Symbol">(</a><a id="11809" href="simple_essence.html#7842" class="Record">LinMap</a> <a id="11816" href="simple_essence.html#11627" class="Bound">T</a> <a id="11818" href="simple_essence.html#11640" class="Bound">A</a><a id="11819" class="Symbol">)</a> <a id="11821" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="11823" href="simple_essence.html#11627" class="Bound">T</a>
<a id="11825" href="simple_essence.html#11618" class="Function">a⊸§↔a</a> <a id="11831" class="Symbol">=</a>
  <a id="11835" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="11839" class="Symbol">{</a><a id="11840" class="Argument">f</a> <a id="11842" class="Symbol">=</a> <a id="11844" href="simple_essence.html#10555" class="Function">a⊸§→a</a><a id="11849" class="Symbol">}</a> <a id="11851" class="Symbol">{</a><a id="11852" class="Argument">f⁻¹</a> <a id="11856" class="Symbol">=</a> <a id="11858" href="simple_essence.html#10854" class="Function">a⊸§←a</a><a id="11863" class="Symbol">}</a>
      <a id="11871" class="Symbol">(</a> <a id="11873" class="Symbol">(λ</a> <a id="11876" class="Symbol">{</a><a id="11877" href="simple_essence.html#11877" class="Bound">x</a> <a id="11879" class="Symbol">→</a> <a id="11881" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="11905" href="simple_essence.html#10555" class="Function">a⊸§→a</a> <a id="11911" class="Symbol">(</a><a id="11912" href="simple_essence.html#10854" class="Function">a⊸§←a</a> <a id="11918" href="simple_essence.html#11877" class="Bound">x</a><a id="11919" class="Symbol">)</a>
                <a id="11937" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="11959" href="simple_essence.html#10555" class="Function">a⊸§→a</a> <a id="11965" class="Symbol">(</a><a id="11966" href="simple_essence.html#8033" class="InductiveConstructor">mkLM</a> <a id="11971" class="Symbol">(</a><a id="11972" href="simple_essence.html#11877" class="Bound">x</a> <a id="11974" href="simple_essence.html#9792" class="Field Operator">⊙_</a><a id="11976" class="Symbol">)</a> <a id="11978" href="simple_essence.html#9870" class="Field">⊙-distrib-+</a> <a id="11990" href="simple_essence.html#10001" class="Field">⊙-comm-·</a><a id="11998" class="Symbol">)</a>
                <a id="12016" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="12038" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12044" class="Symbol">(λ</a> <a id="12047" href="simple_essence.html#12047" class="Bound">acc</a> <a id="12051" href="simple_essence.html#12051" class="Bound">v</a> <a id="12053" class="Symbol">→</a> <a id="12055" href="simple_essence.html#12047" class="Bound">acc</a> <a id="12059" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="12061" class="Symbol">(</a><a id="12062" href="simple_essence.html#11877" class="Bound">x</a> <a id="12064" href="simple_essence.html#9792" class="Field Operator">⊙</a> <a id="12066" href="simple_essence.html#12051" class="Bound">v</a><a id="12067" class="Symbol">)</a> <a id="12069" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="12071" href="simple_essence.html#12051" class="Bound">v</a><a id="12072" class="Symbol">)</a> <a id="12074" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="12076" href="simple_essence.html#9767" class="Field">basisSet</a>
                <a id="12101" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12104" href="simple_essence.html#11155" class="Postulate">x·z≡y·z→x≡y</a> <a id="12116" href="simple_essence.html#10126" class="Field">orthonormal</a> <a id="12128" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="12148" href="simple_essence.html#11877" class="Bound">x</a>
                <a id="12166" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12167" class="Symbol">})</a>
      <a id="12176" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="12178" class="Symbol">λ</a> <a id="12180" class="Symbol">{</a><a id="12181" href="simple_essence.html#12181" class="Bound">lm</a> <a id="12184" class="Symbol">→</a> <a id="12186" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                    <a id="12212" href="simple_essence.html#10854" class="Function">a⊸§←a</a> <a id="12218" class="Symbol">(</a><a id="12219" href="simple_essence.html#10555" class="Function">a⊸§→a</a> <a id="12225" href="simple_essence.html#12181" class="Bound">lm</a><a id="12227" class="Symbol">)</a>
                  <a id="12247" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12271" href="simple_essence.html#10854" class="Function">a⊸§←a</a> <a id="12277" class="Symbol">(</a><a id="12278" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12284" class="Symbol">(λ</a> <a id="12287" href="simple_essence.html#12287" class="Bound">acc</a> <a id="12291" href="simple_essence.html#12291" class="Bound">v</a> <a id="12293" class="Symbol">→</a>
                                     <a id="12332" href="simple_essence.html#12287" class="Bound">acc</a> <a id="12336" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="12338" class="Symbol">(</a><a id="12339" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="12348" href="simple_essence.html#12181" class="Bound">lm</a> <a id="12351" href="simple_essence.html#12291" class="Bound">v</a><a id="12352" class="Symbol">)</a> <a id="12354" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="12356" href="simple_essence.html#12291" class="Bound">v</a><a id="12357" class="Symbol">)</a> <a id="12359" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="12361" href="simple_essence.html#9767" class="Field">basisSet</a><a id="12369" class="Symbol">)</a>
                  <a id="12389" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12413" href="simple_essence.html#8033" class="InductiveConstructor">mkLM</a> <a id="12418" class="Symbol">(</a> <a id="12420" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12426" class="Symbol">(</a> <a id="12428" class="Symbol">λ</a> <a id="12430" href="simple_essence.html#12430" class="Bound">acc</a> <a id="12434" href="simple_essence.html#12434" class="Bound">v</a> <a id="12436" class="Symbol">→</a>
                                     <a id="12475" href="simple_essence.html#12430" class="Bound">acc</a> <a id="12479" href="simple_essence.html#7287" class="Field Operator">+</a> <a id="12481" class="Symbol">(</a><a id="12482" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="12491" href="simple_essence.html#12181" class="Bound">lm</a> <a id="12494" href="simple_essence.html#12434" class="Bound">v</a><a id="12495" class="Symbol">)</a> <a id="12497" href="simple_essence.html#7133" class="Field Operator">·</a> <a id="12499" href="simple_essence.html#12434" class="Bound">v</a>
                                 <a id="12534" class="Symbol">)</a> <a id="12536" href="simple_essence.html#7343" class="Field">𝟘</a> <a id="12538" href="simple_essence.html#9767" class="Field">basisSet</a>
                           <a id="12574" href="simple_essence.html#9792" class="Field Operator">⊙_</a>
                         <a id="12602" class="Symbol">)</a> <a id="12604" href="simple_essence.html#9870" class="Field">⊙-distrib-+</a> <a id="12616" href="simple_essence.html#10001" class="Field">⊙-comm-·</a>
                  <a id="12643" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12646" href="simple_essence.html#8372" class="Postulate">⊸≡</a> <a id="12649" class="Symbol">(</a> <a id="12651" href="simple_essence.html#6434" class="Postulate">extensionality</a>
                            <a id="12694" class="Symbol">(</a> <a id="12696" class="Symbol">λ</a> <a id="12698" href="simple_essence.html#12698" class="Bound">x</a> <a id="12700" class="Symbol">→</a> <a id="12702" href="simple_essence.html#10126" class="Field">orthonormal</a> <a id="12714" class="Symbol">{</a><a id="12715" class="Argument">f</a> <a id="12717" class="Symbol">=</a> <a id="12719" href="simple_essence.html#8050" class="Field">LinMap.f</a> <a id="12728" href="simple_essence.html#12181" class="Bound">lm</a><a id="12730" class="Symbol">}</a> <a id="12732" class="Symbol">{</a><a id="12733" class="Argument">x</a> <a id="12735" class="Symbol">=</a> <a id="12737" href="simple_essence.html#12698" class="Bound">x</a><a id="12738" class="Symbol">}</a> <a id="12740" class="Symbol">)</a>
                        <a id="12766" class="Symbol">)</a>
                   <a id="12787" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                    <a id="12809" href="simple_essence.html#12181" class="Bound">lm</a>
                  <a id="12830" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12831" class="Symbol">}</a>
      <a id="12839" class="Symbol">)</a>

</pre>
### Stashed

Stashed coding attempts.

<pre class="Agda"><a id="12894" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="12977" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="13039" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="13133" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="13196" class="Comment">--</a>
<a id="13199" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="13222" class="Comment">--         ⦃_ : Additive A⦄ ⦃_ : Scalable A⦄</a>
<a id="13267" class="Comment">--         ⦃_ : VectorSpace A⦄</a>
<a id="13298" class="Comment">--         -------------------------------------</a>
<a id="13347" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="13375" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

<a id="13407" class="Comment">-- -- f(0) = 0</a>
<a id="13422" class="Comment">-- zero-lin : {A B : Set a}</a>
<a id="13450" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13501" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13552" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>

<a id="13585" class="Comment">-- -- Injectivity of linear function</a>
<a id="13622" class="Comment">-- inj-lin : {A B : Set a} {x y : A}</a>
<a id="13659" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13710" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13761" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>
<a id="13793" class="Comment">--        → LinMap.f _ x ≡ LinMap.f _ y</a>
<a id="13833" class="Comment">--           ---------------------------</a>
<a id="13874" class="Comment">--        → x ≡ y</a>
<a id="13892" class="Comment">-- inj-lin {x = x} {y = y} fx≡fy =</a>
<a id="13927" class="Comment">--   let f = LinMap.f _</a>
<a id="13951" class="Comment">--    in begin</a>
<a id="13966" class="Comment">--         x</a>
<a id="13979" class="Comment">--       ≡⟨⟩</a>
<a id="13992" class="Comment">--         f (x - y)</a>
<a id="14013" class="Comment">--       ≡⟨ LinMap.adds _ ⟩</a>
<a id="14041" class="Comment">--         f x - f y</a>
<a id="14062" class="Comment">--       ≡⟨ sub-≡ fx≡fy ⟩</a>
<a id="14088" class="Comment">--         0</a>
<a id="14101" class="Comment">--       ≡⟨⟩</a>
<a id="14114" class="Comment">--         y</a>
<a id="14127" class="Comment">--       ∎</a>
      
<a id="14145" class="Comment">-- cong-app′ : ∀ {A : Set a} {B : Set b} {f : A → B} {x y : A}</a>
<a id="14208" class="Comment">--          → f x ≡ f y</a>
<a id="14232" class="Comment">--             ---------</a>
<a id="14257" class="Comment">--          → x ≡ y</a>
<a id="14277" class="Comment">-- cong-app′ fx≡fy = {!contraposition!}</a>
         
<a id="14327" class="Comment">-- x·z≡y·z→x≡y : {A : Set a}</a>
<a id="14356" class="Comment">--                ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="14412" class="Comment">--                ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="14471" class="Comment">--                {x y : A}</a>
<a id="14499" class="Comment">--             → (∀ {z : A} → x · z ≡ y · z)</a>
<a id="14544" class="Comment">--                ------------------------------------------------------------</a>
<a id="14623" class="Comment">--             → x ≡ y</a>
<a id="14646" class="Comment">-- x·z≡y·z→x≡y {x = x} {y = y} g =</a>
<a id="14681" class="Comment">--   let f = LinMap.f _</a>
<a id="14705" class="Comment">--       z = foldl (λ acc v → acc ⊕ f v ⊛ v) id⊕ basisSet</a>
<a id="14763" class="Comment">--       x·z≡y·z = g {z}</a>
<a id="14788" class="Comment">--    in cong-app refl {!!}</a>
<a id="14816" class="Comment">--    -- in begin</a>
<a id="14834" class="Comment">--    --      -- ?</a>
<a id="14853" class="Comment">--    --      x·z≡y·z</a>
<a id="14875" class="Comment">--    --    -- ≡⟨ ? ⟩</a>
<a id="14897" class="Comment">--    --    --   x · z ≡ y · z</a>
<a id="14928" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="14947" class="Comment">--    --    -- ≡⟨ cong (_≡ y · z) comm-· ⟩</a>
<a id="14990" class="Comment">--    --      z · x ≡ y · z</a>
<a id="15018" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15037" class="Comment">--    --    -- ≡⟨ cong (z · x ≡_) comm-· ⟩</a>
<a id="15080" class="Comment">--    --      z · x ≡ z · y</a>
<a id="15108" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15127" class="Comment">--    --    -- ≡⟨ cong (_≡ z · y) (orthonormal) ⟩</a>
<a id="15177" class="Comment">--    --      f x ≡ z · y</a>
<a id="15203" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15222" class="Comment">--    --    -- ≡⟨ cong (f x ≡_) (orthonormal) ⟩</a>
<a id="15270" class="Comment">--    --      f x ≡ f y</a>
<a id="15294" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15313" class="Comment">--    --    -- ≡⟨ cong-app ⟩</a>
<a id="15342" class="Comment">--    --      x ≡ y</a>
<a id="15362" class="Comment">--    --    ∎</a>

<a id="15377" class="Comment">-- -- So, how was Agsy able to jump over all of that?</a>
<a id="15431" class="Comment">-- -- My usual experience w/ Agsy is that when I ask it to solve anything</a>
<a id="15505" class="Comment">-- -- non-trivial by itself it always complains, &quot;Sorry, I don&#39;t support</a>
<a id="15578" class="Comment">-- -- literals, yet.&quot;, which I&#39;ve never understood.</a>

<a id="15631" class="Comment">-- a⊸§↔a : {A : Set a}</a>
<a id="15654" class="Comment">--          ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="15704" class="Comment">--          ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="15757" class="Comment">--          -----------------------------------------</a>
<a id="15811" class="Comment">--       → (LinMap A §) ↔ A</a>
<a id="15839" class="Comment">-- a⊸§↔a {A} =</a>
<a id="15854" class="Comment">--   mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}</a>
<a id="15889" class="Comment">--       ( (λ {x → begin</a>
<a id="15914" class="Comment">--                   a⊸§→a (a⊸§←a x)</a>
<a id="15951" class="Comment">--                 ≡⟨⟩</a>
<a id="15974" class="Comment">--                   a⊸§→a (mkLM (x ·_) ·-distrib-⊕ ·-comm-⊛)</a>
<a id="16036" class="Comment">--                 ≡⟨⟩</a>
<a id="16059" class="Comment">--                   foldl (λ acc v → acc ⊕ (x · v) ⊛ v) id⊕ basisSet</a>
<a id="16129" class="Comment">--                 ≡⟨ x·z≡y·z→x≡y (orthonormal {f = (x ·_)}) ⟩</a>
<a id="16192" class="Comment">--                   x</a>
<a id="16215" class="Comment">--                 ∎})</a>
<a id="16238" class="Comment">--       , λ {lm → begin</a>
<a id="16263" class="Comment">--                   a⊸§←a (a⊸§→a lm)</a>
<a id="16301" class="Comment">--                 ≡⟨⟩</a>
<a id="16324" class="Comment">--                   a⊸§←a (foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)</a>
<a id="16410" class="Comment">--                 ≡⟨⟩</a>
<a id="16433" class="Comment">--                   mkLM ((foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)·_)</a>
<a id="16522" class="Comment">--                        ·-distrib-⊕ ·-comm-⊛</a>
<a id="16569" class="Comment">--                 ≡⟨ ⊸≡ ( extensionality</a>
<a id="16611" class="Comment">--                           ( λ x → orthonormal {f = LinMap.f lm} {x = x} )</a>
<a id="16688" class="Comment">--                       )</a>
<a id="16715" class="Comment">--                  ⟩</a>
<a id="16737" class="Comment">--                   lm</a>
<a id="16761" class="Comment">--                 ∎}</a>
<a id="16783" class="Comment">--       )</a>


</pre>