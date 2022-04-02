---
format: 'markdown+latex'
title: 'Agda Doodlings Involving Linearity & Vector Spaces'
description: Agda proofs of some isomorphisms revealed by Conal in his paper.
author: 'David Banas <capn.freako@gmail.com>'
date: 2022-04-02
copy: Copyright (c) 2022 David Banas; all rights reserved World wide.
...

{% include mathjax.html %}

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

<link rel="stylesheet" type="text/css" href="Agda.css">

<pre class="Agda"><a id="5555" class="Keyword">module</a> <a id="5562" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5577" class="Symbol">{</a><a id="5578" href="simple_essence.html#5578" class="Bound">s</a> <a id="5580" href="simple_essence.html#5580" class="Bound">a</a> <a id="5582" href="simple_essence.html#5582" class="Bound">b</a><a id="5583" class="Symbol">}</a> <a id="5585" class="Keyword">where</a>

<a id="5592" class="Keyword">open</a> <a id="5597" class="Keyword">import</a> <a id="5604" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5623" class="Keyword">open</a> <a id="5628" class="Keyword">import</a> <a id="5635" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5670" class="Keyword">using</a> <a id="5676" class="Symbol">(</a><a id="5677" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5691" class="Symbol">)</a>
<a id="5693" class="Keyword">open</a> <a id="5698" class="Keyword">import</a> <a id="5705" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5716" class="Keyword">open</a> <a id="5721" class="Keyword">import</a> <a id="5728" href="Data.List.html" class="Module">Data.List</a>
<a id="5738" class="Keyword">open</a> <a id="5743" class="Keyword">import</a> <a id="5750" href="Function.html" class="Module">Function</a> <a id="5759" class="Keyword">using</a> <a id="5765" class="Symbol">(</a><a id="5766" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5769" class="Symbol">;</a> <a id="5771" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5774" class="Symbol">;</a> <a id="5776" href="Function.Base.html#615" class="Function">id</a><a id="5778" class="Symbol">)</a>
<a id="5780" class="Keyword">open</a> <a id="5785" class="Keyword">import</a> <a id="5792" href="Level.html" class="Module">Level</a> <a id="5798" class="Keyword">using</a> <a id="5804" class="Symbol">(</a><a id="5805" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5810" class="Symbol">;</a> <a id="5812" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5815" class="Symbol">)</a>

<a id="5818" class="Keyword">import</a> <a id="5825" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5863" class="Symbol">as</a> <a id="5866" class="Module">Eq</a>
<a id="5869" class="Keyword">open</a> <a id="5874" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5877" class="Keyword">using</a> <a id="5883" class="Symbol">(</a><a id="5884" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5887" class="Symbol">;</a> <a id="5889" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5893" class="Symbol">;</a> <a id="5895" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5900" class="Symbol">;</a> <a id="5902" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5905" class="Symbol">;</a> <a id="5907" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5911" class="Symbol">;</a> <a id="5913" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5918" class="Symbol">;</a> <a id="5920" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5928" class="Symbol">;</a> <a id="5930" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5935" class="Symbol">)</a>
<a id="5937" class="Keyword">open</a> <a id="5942" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5957" class="Keyword">using</a> <a id="5963" class="Symbol">(</a><a id="5964" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5970" class="Symbol">;</a> <a id="5972" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5977" class="Symbol">;</a> <a id="5979" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5985" class="Symbol">;</a> <a id="5987" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5989" class="Symbol">)</a>

<a id="5992" class="Keyword">postulate</a>
  <a id="6004" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="6079" href="simple_essence.html#6079" class="Postulate">id+</a> <a id="6083" class="Symbol">:</a> <a id="6085" class="Symbol">{</a><a id="6086" href="simple_essence.html#6086" class="Bound">x</a> <a id="6088" class="Symbol">:</a> <a id="6090" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="6095" class="Symbol">}</a> <a id="6097" class="Symbol">→</a> <a id="6099" class="Number">0.0</a> <a id="6103" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6105" href="simple_essence.html#6086" class="Bound">x</a> <a id="6107" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6109" href="simple_essence.html#6086" class="Bound">x</a>
  <a id="extensionality"></a><a id="6113" href="simple_essence.html#6113" class="Postulate">extensionality</a> <a id="6128" class="Symbol">:</a> <a id="6130" class="Symbol">∀</a> <a id="6132" class="Symbol">{</a><a id="6133" href="simple_essence.html#6133" class="Bound">ℓ₁</a> <a id="6136" href="simple_essence.html#6136" class="Bound">ℓ₂</a><a id="6138" class="Symbol">}</a> <a id="6140" class="Symbol">→</a> <a id="6142" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="6157" href="simple_essence.html#6133" class="Bound">ℓ₁</a> <a id="6160" href="simple_essence.html#6136" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="6164" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="6166" class="Symbol">:</a> <a id="6168" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="6174" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="6176" class="Symbol">=</a> <a id="6178" href="simple_essence.html#5578" class="Bound">s</a> <a id="6180" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6182" href="simple_essence.html#5580" class="Bound">a</a> <a id="6184" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6186" href="simple_essence.html#5582" class="Bound">b</a>

<a id="6189" class="Keyword">data</a> <a id="§"></a><a id="6194" href="simple_essence.html#6194" class="Datatype">§</a> <a id="6196" class="Symbol">:</a> <a id="6198" class="PrimitiveType">Set</a> <a id="6202" href="simple_essence.html#5580" class="Bound">a</a> <a id="6204" class="Keyword">where</a>
  <a id="§.S"></a><a id="6212" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6214" class="Symbol">:</a> <a id="6216" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="6222" class="Symbol">→</a> <a id="6224" href="simple_essence.html#6194" class="Datatype">§</a>

<a id="6227" class="Keyword">record</a> <a id="Additive"></a><a id="6234" href="simple_essence.html#6234" class="Record">Additive</a> <a id="6243" class="Symbol">(</a><a id="6244" href="simple_essence.html#6244" class="Bound">A</a> <a id="6246" class="Symbol">:</a> <a id="6248" class="PrimitiveType">Set</a> <a id="6252" href="simple_essence.html#5580" class="Bound">a</a><a id="6253" class="Symbol">)</a> <a id="6255" class="Symbol">:</a> <a id="6257" class="PrimitiveType">Set</a> <a id="6261" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="6263" class="Keyword">where</a>
  <a id="6271" class="Keyword">infixl</a> <a id="6278" class="Number">6</a> <a id="6280" href="simple_essence.html#6360" class="Field Operator">_⊕_</a>  <a id="6285" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6337" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6347" href="simple_essence.html#6347" class="Field">id⊕</a>  <a id="6352" class="Symbol">:</a> <a id="6354" href="simple_essence.html#6244" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6360" href="simple_essence.html#6360" class="Field Operator">_⊕_</a>  <a id="6365" class="Symbol">:</a> <a id="6367" href="simple_essence.html#6244" class="Bound">A</a> <a id="6369" class="Symbol">→</a> <a id="6371" href="simple_essence.html#6244" class="Bound">A</a> <a id="6373" class="Symbol">→</a> <a id="6375" href="simple_essence.html#6244" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6381" href="simple_essence.html#6381" class="Field">id-⊕</a> <a id="6386" class="Symbol">:</a> <a id="6388" class="Symbol">(</a><a id="6389" href="simple_essence.html#6389" class="Bound">a</a> <a id="6391" class="Symbol">:</a> <a id="6393" href="simple_essence.html#6244" class="Bound">A</a><a id="6394" class="Symbol">)</a>
           <a id="6407" class="Comment">-----------</a>
         <a id="6428" class="Symbol">→</a> <a id="6430" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="6434" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="6436" href="simple_essence.html#6389" class="Bound">a</a> <a id="6438" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6440" href="simple_essence.html#6389" class="Bound">a</a>
    <a id="6446" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6499" class="Keyword">open</a> <a id="6504" href="simple_essence.html#6234" class="Module">Additive</a> <a id="6513" class="Symbol">{{</a> <a id="6516" class="Symbol">...</a> <a id="6520" class="Symbol">}}</a>
<a id="6523" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6534" href="simple_essence.html#6534" class="Function">AdditiveScalar</a> <a id="6549" class="Symbol">:</a> <a id="6551" href="simple_essence.html#6234" class="Record">Additive</a> <a id="6560" href="simple_essence.html#6194" class="Datatype">§</a>
  <a id="6564" href="simple_essence.html#6534" class="Function">AdditiveScalar</a> <a id="6579" class="Symbol">=</a> <a id="6581" class="Keyword">record</a>
    <a id="6592" class="Symbol">{</a> <a id="6594" href="simple_essence.html#6347" class="Field">id⊕</a>  <a id="6599" class="Symbol">=</a> <a id="6601" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6603" class="Number">0.0</a>
    <a id="6611" class="Symbol">;</a> <a id="6613" href="simple_essence.html#6360" class="Field Operator">_⊕_</a>  <a id="6618" class="Symbol">=</a> <a id="6620" class="Symbol">λ</a> <a id="6622" class="Symbol">{(</a><a id="6624" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6626" href="simple_essence.html#6626" class="Bound">x</a><a id="6627" class="Symbol">)</a> <a id="6629" class="Symbol">(</a><a id="6630" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6632" href="simple_essence.html#6632" class="Bound">y</a><a id="6633" class="Symbol">)</a> <a id="6635" class="Symbol">→</a> <a id="6637" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6639" class="Symbol">(</a><a id="6640" href="simple_essence.html#6626" class="Bound">x</a> <a id="6642" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6644" href="simple_essence.html#6632" class="Bound">y</a><a id="6645" class="Symbol">)}</a>
    <a id="6652" class="Symbol">;</a> <a id="6654" href="simple_essence.html#6381" class="Field">id-⊕</a> <a id="6659" class="Symbol">=</a> <a id="6661" class="Symbol">λ</a> <a id="6663" class="Symbol">{</a> <a id="6665" class="Symbol">(</a><a id="6666" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6668" href="simple_essence.html#6668" class="Bound">x</a><a id="6669" class="Symbol">)</a> <a id="6671" class="Symbol">→</a> <a id="6673" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6706" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6708" class="Symbol">(</a><a id="6709" class="Number">0.0</a> <a id="6713" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6715" href="simple_essence.html#6668" class="Bound">x</a><a id="6716" class="Symbol">)</a>
                         <a id="6743" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6746" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6751" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6753" href="simple_essence.html#6079" class="Postulate">id+</a> <a id="6757" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6786" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6788" href="simple_essence.html#6668" class="Bound">x</a>
                         <a id="6815" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6832" class="Symbol">}</a>
    <a id="6838" class="Symbol">}</a>

<a id="6841" class="Keyword">record</a> <a id="Scalable"></a><a id="6848" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="6857" class="Symbol">(</a><a id="6858" href="simple_essence.html#6858" class="Bound">A</a> <a id="6860" class="Symbol">:</a> <a id="6862" class="PrimitiveType">Set</a> <a id="6866" href="simple_essence.html#5580" class="Bound">a</a><a id="6867" class="Symbol">)</a> <a id="6869" class="Symbol">:</a> <a id="6871" class="PrimitiveType">Set</a> <a id="6875" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="6877" class="Keyword">where</a>
  <a id="6885" class="Keyword">infixl</a> <a id="6892" class="Number">7</a> <a id="6894" href="simple_essence.html#6961" class="Field Operator">_⊛_</a>  <a id="6899" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6951" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6961" href="simple_essence.html#6961" class="Field Operator">_⊛_</a> <a id="6965" class="Symbol">:</a> <a id="6967" href="simple_essence.html#6194" class="Datatype">§</a> <a id="6969" class="Symbol">→</a> <a id="6971" href="simple_essence.html#6858" class="Bound">A</a> <a id="6973" class="Symbol">→</a> <a id="6975" href="simple_essence.html#6858" class="Bound">A</a>
<a id="6977" class="Keyword">open</a> <a id="6982" href="simple_essence.html#6848" class="Module">Scalable</a> <a id="6991" class="Symbol">{{</a> <a id="6994" class="Symbol">...</a> <a id="6998" class="Symbol">}}</a>
<a id="7001" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="7012" href="simple_essence.html#7012" class="Function">ScalableScalar</a> <a id="7027" class="Symbol">:</a> <a id="7029" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="7038" href="simple_essence.html#6194" class="Datatype">§</a>
  <a id="7042" href="simple_essence.html#7012" class="Function">ScalableScalar</a> <a id="7057" class="Symbol">=</a> <a id="7059" class="Keyword">record</a>
    <a id="7070" class="Symbol">{</a> <a id="7072" href="simple_essence.html#6961" class="Field Operator">_⊛_</a> <a id="7076" class="Symbol">=</a> <a id="7078" class="Symbol">λ</a> <a id="7080" class="Symbol">{(</a><a id="7082" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="7084" href="simple_essence.html#7084" class="Bound">x</a><a id="7085" class="Symbol">)</a> <a id="7087" class="Symbol">(</a><a id="7088" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="7090" href="simple_essence.html#7090" class="Bound">y</a><a id="7091" class="Symbol">)</a> <a id="7093" class="Symbol">→</a> <a id="7095" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="7097" class="Symbol">(</a><a id="7098" href="simple_essence.html#7084" class="Bound">x</a> <a id="7100" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="7102" href="simple_essence.html#7090" class="Bound">y</a><a id="7103" class="Symbol">)}</a>
    <a id="7110" class="Symbol">}</a>

<a id="7113" class="Keyword">record</a> <a id="LinMap"></a><a id="7120" href="simple_essence.html#7120" class="Record">LinMap</a> <a id="7127" class="Symbol">(</a><a id="7128" href="simple_essence.html#7128" class="Bound">A</a> <a id="7130" class="Symbol">:</a> <a id="7132" class="PrimitiveType">Set</a> <a id="7136" href="simple_essence.html#5580" class="Bound">a</a><a id="7137" class="Symbol">)</a> <a id="7139" class="Symbol">(</a><a id="7140" href="simple_essence.html#7140" class="Bound">B</a> <a id="7142" class="Symbol">:</a> <a id="7144" class="PrimitiveType">Set</a> <a id="7148" href="simple_essence.html#5580" class="Bound">a</a><a id="7149" class="Symbol">)</a>
              <a id="7165" class="Symbol">{{</a><a id="7167" href="simple_essence.html#7167" class="Bound">_</a> <a id="7169" class="Symbol">:</a> <a id="7171" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7180" href="simple_essence.html#7128" class="Bound">A</a><a id="7181" class="Symbol">}}</a> <a id="7184" class="Symbol">{{</a><a id="7186" href="simple_essence.html#7186" class="Bound">_</a> <a id="7188" class="Symbol">:</a> <a id="7190" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7199" href="simple_essence.html#7140" class="Bound">B</a><a id="7200" class="Symbol">}}</a>
              <a id="7217" class="Symbol">{{</a><a id="7219" href="simple_essence.html#7219" class="Bound">_</a> <a id="7221" class="Symbol">:</a> <a id="7223" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="7232" href="simple_essence.html#7128" class="Bound">A</a><a id="7233" class="Symbol">}}</a> <a id="7236" class="Symbol">{{</a><a id="7238" href="simple_essence.html#7238" class="Bound">_</a> <a id="7240" class="Symbol">:</a> <a id="7242" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="7251" href="simple_essence.html#7140" class="Bound">B</a><a id="7252" class="Symbol">}}</a>
              <a id="7269" class="Symbol">:</a> <a id="7271" class="PrimitiveType">Set</a> <a id="7275" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="7277" class="Keyword">where</a>
  <a id="7285" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7297" href="simple_essence.html#7297" class="InductiveConstructor">mkLM</a>
  <a id="7304" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7314" href="simple_essence.html#7314" class="Field">f</a>      <a id="7321" class="Symbol">:</a> <a id="7323" href="simple_essence.html#7128" class="Bound">A</a> <a id="7325" class="Symbol">→</a> <a id="7327" href="simple_essence.html#7140" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7334" href="simple_essence.html#7334" class="Field">adds</a>   <a id="7341" class="Symbol">:</a> <a id="7343" class="Symbol">∀</a> <a id="7345" class="Symbol">{</a><a id="7346" href="simple_essence.html#7346" class="Bound">a</a> <a id="7348" href="simple_essence.html#7348" class="Bound">b</a> <a id="7350" class="Symbol">:</a> <a id="7352" href="simple_essence.html#7128" class="Bound">A</a><a id="7353" class="Symbol">}</a>
             <a id="7368" class="Comment">---------------------</a>
           <a id="7401" class="Symbol">→</a> <a id="7403" href="simple_essence.html#7314" class="Field">f</a> <a id="7405" class="Symbol">(</a><a id="7406" href="simple_essence.html#7346" class="Bound">a</a> <a id="7408" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="7410" href="simple_essence.html#7348" class="Bound">b</a><a id="7411" class="Symbol">)</a> <a id="7413" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7415" href="simple_essence.html#7314" class="Field">f</a> <a id="7417" href="simple_essence.html#7346" class="Bound">a</a> <a id="7419" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="7421" href="simple_essence.html#7314" class="Field">f</a> <a id="7423" href="simple_essence.html#7348" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7430" href="simple_essence.html#7430" class="Field">scales</a> <a id="7437" class="Symbol">:</a> <a id="7439" class="Symbol">∀</a> <a id="7441" class="Symbol">{</a><a id="7442" href="simple_essence.html#7442" class="Bound">s</a> <a id="7444" class="Symbol">:</a> <a id="7446" href="simple_essence.html#6194" class="Datatype">§</a><a id="7447" class="Symbol">}</a> <a id="7449" class="Symbol">{</a><a id="7450" href="simple_essence.html#7450" class="Bound">a</a> <a id="7452" class="Symbol">:</a> <a id="7454" href="simple_essence.html#7128" class="Bound">A</a><a id="7455" class="Symbol">}</a>
             <a id="7470" class="Comment">-------------------</a>
           <a id="7501" class="Symbol">→</a> <a id="7503" href="simple_essence.html#7314" class="Field">f</a> <a id="7505" class="Symbol">(</a><a id="7506" href="simple_essence.html#7442" class="Bound">s</a> <a id="7508" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="7510" href="simple_essence.html#7450" class="Bound">a</a><a id="7511" class="Symbol">)</a> <a id="7513" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7515" href="simple_essence.html#7442" class="Bound">s</a> <a id="7517" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="7519" href="simple_essence.html#7314" class="Field">f</a> <a id="7521" href="simple_essence.html#7450" class="Bound">a</a>
<a id="7523" class="Keyword">open</a> <a id="7528" href="simple_essence.html#7120" class="Module">LinMap</a> <a id="7535" class="Symbol">{{</a> <a id="7538" class="Symbol">...</a> <a id="7542" class="Symbol">}}</a>

<a id="7546" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7572" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7620" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7632" href="simple_essence.html#7632" class="Postulate">⊸≡</a> <a id="7635" class="Symbol">:</a> <a id="7637" class="Symbol">{</a><a id="7638" href="simple_essence.html#7638" class="Bound">A</a> <a id="7640" href="simple_essence.html#7640" class="Bound">B</a> <a id="7642" class="Symbol">:</a> <a id="7644" class="PrimitiveType">Set</a> <a id="7648" href="simple_essence.html#5580" class="Bound">a</a><a id="7649" class="Symbol">}</a>
       <a id="7658" class="Symbol">{{</a><a id="7660" href="simple_essence.html#7660" class="Bound">_</a> <a id="7662" class="Symbol">:</a> <a id="7664" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7673" href="simple_essence.html#7638" class="Bound">A</a><a id="7674" class="Symbol">}}</a> <a id="7677" class="Symbol">{{</a><a id="7679" href="simple_essence.html#7679" class="Bound">_</a> <a id="7681" class="Symbol">:</a> <a id="7683" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7692" href="simple_essence.html#7640" class="Bound">B</a><a id="7693" class="Symbol">}}</a>
       <a id="7703" class="Symbol">{{</a><a id="7705" href="simple_essence.html#7705" class="Bound">_</a> <a id="7707" class="Symbol">:</a> <a id="7709" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="7718" href="simple_essence.html#7638" class="Bound">A</a><a id="7719" class="Symbol">}}</a> <a id="7722" class="Symbol">{{</a><a id="7724" href="simple_essence.html#7724" class="Bound">_</a> <a id="7726" class="Symbol">:</a> <a id="7728" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="7737" href="simple_essence.html#7640" class="Bound">B</a><a id="7738" class="Symbol">}}</a>
       <a id="7748" class="Symbol">{</a><a id="7749" href="simple_essence.html#7749" class="Bound">lm₁</a> <a id="7753" href="simple_essence.html#7753" class="Bound">lm₂</a> <a id="7757" class="Symbol">:</a> <a id="7759" href="simple_essence.html#7120" class="Record">LinMap</a> <a id="7766" href="simple_essence.html#7638" class="Bound">A</a> <a id="7768" href="simple_essence.html#7640" class="Bound">B</a><a id="7769" class="Symbol">}</a>
     <a id="7776" class="Symbol">→</a> <a id="7778" href="simple_essence.html#7314" class="Field">LinMap.f</a> <a id="7787" href="simple_essence.html#7749" class="Bound">lm₁</a> <a id="7791" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7793" href="simple_essence.html#7314" class="Field">LinMap.f</a> <a id="7802" href="simple_essence.html#7753" class="Bound">lm₂</a>
       <a id="7813" class="Comment">---------------------------</a>
     <a id="7846" class="Symbol">→</a> <a id="7848" href="simple_essence.html#7749" class="Bound">lm₁</a> <a id="7852" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7854" href="simple_essence.html#7753" class="Bound">lm₂</a>

<a id="7859" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7866" href="simple_essence.html#7866" class="Record">VectorSpace</a> <a id="7878" class="Symbol">(</a><a id="7879" href="simple_essence.html#7879" class="Bound">A</a> <a id="7881" class="Symbol">:</a> <a id="7883" class="PrimitiveType">Set</a> <a id="7887" href="simple_essence.html#5580" class="Bound">a</a><a id="7888" class="Symbol">)</a>
                   <a id="7909" class="Symbol">{{</a><a id="7911" href="simple_essence.html#7911" class="Bound">_</a> <a id="7913" class="Symbol">:</a> <a id="7915" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7924" href="simple_essence.html#7879" class="Bound">A</a><a id="7925" class="Symbol">}}</a> <a id="7928" class="Symbol">{{</a><a id="7930" href="simple_essence.html#7930" class="Bound">_</a> <a id="7932" class="Symbol">:</a> <a id="7934" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="7943" href="simple_essence.html#7879" class="Bound">A</a><a id="7944" class="Symbol">}}</a>
                   <a id="7966" class="Symbol">:</a> <a id="7968" class="PrimitiveType">Set</a> <a id="7972" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="7974" class="Keyword">where</a>
  <a id="7982" class="Keyword">field</a>
    <a id="7992" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="8086" href="simple_essence.html#8086" class="Field">basisSet</a>    <a id="8098" class="Symbol">:</a> <a id="8100" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="8105" href="simple_essence.html#7879" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="8111" href="simple_essence.html#8111" class="Field Operator">_·_</a>         <a id="8123" class="Symbol">:</a> <a id="8125" href="simple_essence.html#7879" class="Bound">A</a> <a id="8127" class="Symbol">→</a> <a id="8129" href="simple_essence.html#7879" class="Bound">A</a> <a id="8131" class="Symbol">→</a> <a id="8133" href="simple_essence.html#6194" class="Datatype">§</a>
    <a id="8139" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="8189" href="simple_essence.html#8189" class="Field">·-distrib-⊕</a> <a id="8201" class="Symbol">:</a> <a id="8203" class="Symbol">∀</a> <a id="8205" class="Symbol">{</a><a id="8206" href="simple_essence.html#8206" class="Bound">a</a> <a id="8208" href="simple_essence.html#8208" class="Bound">b</a> <a id="8210" href="simple_essence.html#8210" class="Bound">c</a> <a id="8212" class="Symbol">:</a> <a id="8214" href="simple_essence.html#7879" class="Bound">A</a><a id="8215" class="Symbol">}</a>
                  <a id="8235" class="Comment">-------------------------------</a>
                <a id="8283" class="Symbol">→</a> <a id="8285" href="simple_essence.html#8206" class="Bound">a</a> <a id="8287" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="8289" class="Symbol">(</a><a id="8290" href="simple_essence.html#8208" class="Bound">b</a> <a id="8292" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="8294" href="simple_essence.html#8210" class="Bound">c</a><a id="8295" class="Symbol">)</a> <a id="8297" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8299" class="Symbol">(</a><a id="8300" href="simple_essence.html#8206" class="Bound">a</a> <a id="8302" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="8304" href="simple_essence.html#8208" class="Bound">b</a><a id="8305" class="Symbol">)</a> <a id="8307" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="8309" class="Symbol">(</a><a id="8310" href="simple_essence.html#8206" class="Bound">a</a> <a id="8312" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="8314" href="simple_essence.html#8210" class="Bound">c</a><a id="8315" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8321" href="simple_essence.html#8321" class="Field">·-comm-⊛</a>    <a id="8333" class="Symbol">:</a> <a id="8335" class="Symbol">∀</a> <a id="8337" class="Symbol">{</a><a id="8338" href="simple_essence.html#8338" class="Bound">s</a> <a id="8340" class="Symbol">:</a> <a id="8342" href="simple_essence.html#6194" class="Datatype">§</a><a id="8343" class="Symbol">}</a> <a id="8345" class="Symbol">{</a><a id="8346" href="simple_essence.html#8346" class="Bound">a</a> <a id="8348" href="simple_essence.html#8348" class="Bound">b</a> <a id="8350" class="Symbol">:</a> <a id="8352" href="simple_essence.html#7879" class="Bound">A</a><a id="8353" class="Symbol">}</a>
                  <a id="8373" class="Comment">-------------------------</a>
                <a id="8415" class="Symbol">→</a> <a id="8417" href="simple_essence.html#8346" class="Bound">a</a> <a id="8419" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="8421" class="Symbol">(</a><a id="8422" href="simple_essence.html#8338" class="Bound">s</a> <a id="8424" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="8426" href="simple_essence.html#8348" class="Bound">b</a><a id="8427" class="Symbol">)</a> <a id="8429" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8431" href="simple_essence.html#8338" class="Bound">s</a> <a id="8433" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="8435" class="Symbol">(</a><a id="8436" href="simple_essence.html#8346" class="Bound">a</a> <a id="8438" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="8440" href="simple_essence.html#8348" class="Bound">b</a><a id="8441" class="Symbol">)</a>
    <a id="8447" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8531" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8589" href="simple_essence.html#8589" class="Field">orthonormal</a> <a id="8601" class="Symbol">:</a> <a id="8603" class="Symbol">∀</a> <a id="8605" class="Symbol">{</a><a id="8606" href="simple_essence.html#8606" class="Bound">f</a> <a id="8608" class="Symbol">:</a> <a id="8610" href="simple_essence.html#7879" class="Bound">A</a> <a id="8612" class="Symbol">→</a> <a id="8614" href="simple_essence.html#6194" class="Datatype">§</a><a id="8615" class="Symbol">}</a>
                <a id="8633" class="Symbol">→</a> <a id="8635" class="Symbol">{</a><a id="8636" href="simple_essence.html#8636" class="Bound">x</a> <a id="8638" class="Symbol">:</a> <a id="8640" href="simple_essence.html#7879" class="Bound">A</a><a id="8641" class="Symbol">}</a>
                  <a id="8661" class="Comment">----------------------------------------------------------</a>
                <a id="8736" class="Symbol">→</a> <a id="8738" class="Symbol">(</a><a id="8739" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8745" class="Symbol">(λ</a> <a id="8748" href="simple_essence.html#8748" class="Bound">acc</a> <a id="8752" href="simple_essence.html#8752" class="Bound">v</a> <a id="8754" class="Symbol">→</a> <a id="8756" href="simple_essence.html#8748" class="Bound">acc</a> <a id="8760" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="8762" class="Symbol">(</a><a id="8763" href="simple_essence.html#8606" class="Bound">f</a> <a id="8765" href="simple_essence.html#8752" class="Bound">v</a><a id="8766" class="Symbol">)</a> <a id="8768" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="8770" href="simple_essence.html#8752" class="Bound">v</a><a id="8771" class="Symbol">)</a> <a id="8773" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="8777" href="simple_essence.html#8086" class="Field">basisSet</a><a id="8785" class="Symbol">)</a> <a id="8787" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="8789" href="simple_essence.html#8636" class="Bound">x</a> <a id="8791" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8793" href="simple_essence.html#8606" class="Bound">f</a> <a id="8795" href="simple_essence.html#8636" class="Bound">x</a>
<a id="8797" class="Keyword">open</a> <a id="8802" href="simple_essence.html#7866" class="Module">VectorSpace</a> <a id="8814" class="Symbol">{{</a> <a id="8817" class="Symbol">...</a> <a id="8821" class="Symbol">}}</a>

<a id="8825" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8865" href="simple_essence.html#8865" class="Function">a⊸§→a</a> <a id="8871" class="Symbol">:</a> <a id="8873" class="Symbol">{</a><a id="8874" href="simple_essence.html#8874" class="Bound">A</a> <a id="8876" class="Symbol">:</a> <a id="8878" class="PrimitiveType">Set</a> <a id="8882" href="simple_essence.html#5580" class="Bound">a</a><a id="8883" class="Symbol">}</a>
        <a id="8893" class="Symbol">{{</a><a id="8895" href="simple_essence.html#8895" class="Bound">_</a> <a id="8897" class="Symbol">:</a> <a id="8899" href="simple_essence.html#6234" class="Record">Additive</a> <a id="8908" href="simple_essence.html#8874" class="Bound">A</a><a id="8909" class="Symbol">}}</a> <a id="8912" class="Symbol">{{</a><a id="8914" href="simple_essence.html#8914" class="Bound">_</a> <a id="8916" class="Symbol">:</a> <a id="8918" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="8927" href="simple_essence.html#8874" class="Bound">A</a><a id="8928" class="Symbol">}}</a>
        <a id="8939" class="Symbol">{{</a><a id="8941" href="simple_essence.html#8941" class="Bound">_</a> <a id="8943" class="Symbol">:</a> <a id="8945" href="simple_essence.html#7866" class="Record">VectorSpace</a> <a id="8957" href="simple_essence.html#8874" class="Bound">A</a><a id="8958" class="Symbol">}}</a>
        <a id="8969" class="Comment">-------------------------------------</a>
      <a id="9013" class="Symbol">→</a> <a id="9015" href="simple_essence.html#7120" class="Record">LinMap</a> <a id="9022" href="simple_essence.html#8874" class="Bound">A</a> <a id="9024" href="simple_essence.html#6194" class="Datatype">§</a> <a id="9026" class="Symbol">→</a> <a id="9028" href="simple_essence.html#8874" class="Bound">A</a>
<a id="9030" href="simple_essence.html#8865" class="Function">a⊸§→a</a> <a id="9036" class="Symbol">=</a> <a id="9038" class="Symbol">λ</a> <a id="9040" class="Symbol">{</a> <a id="9042" href="simple_essence.html#9042" class="Bound">lm</a> <a id="9045" class="Symbol">→</a> <a id="9047" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="9053" class="Symbol">(λ</a> <a id="9056" href="simple_essence.html#9056" class="Bound">acc</a> <a id="9060" href="simple_essence.html#9060" class="Bound">v</a> <a id="9062" class="Symbol">→</a> <a id="9064" href="simple_essence.html#9056" class="Bound">acc</a> <a id="9068" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="9070" class="Symbol">(</a><a id="9071" href="simple_essence.html#7314" class="Field">LinMap.f</a> <a id="9080" href="simple_essence.html#9042" class="Bound">lm</a> <a id="9083" href="simple_essence.html#9060" class="Bound">v</a><a id="9084" class="Symbol">)</a> <a id="9086" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="9088" href="simple_essence.html#9060" class="Bound">v</a><a id="9089" class="Symbol">)</a> <a id="9091" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="9095" href="simple_essence.html#8086" class="Field">basisSet</a> <a id="9104" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="9107" href="simple_essence.html#9107" class="Function">a⊸§←a</a> <a id="9113" class="Symbol">:</a> <a id="9115" class="Symbol">{</a><a id="9116" href="simple_essence.html#9116" class="Bound">A</a> <a id="9118" class="Symbol">:</a> <a id="9120" class="PrimitiveType">Set</a> <a id="9124" href="simple_essence.html#5580" class="Bound">a</a><a id="9125" class="Symbol">}</a>
        <a id="9135" class="Symbol">{{</a><a id="9137" href="simple_essence.html#9137" class="Bound">_</a> <a id="9139" class="Symbol">:</a> <a id="9141" href="simple_essence.html#6234" class="Record">Additive</a> <a id="9150" href="simple_essence.html#9116" class="Bound">A</a><a id="9151" class="Symbol">}}</a> <a id="9154" class="Symbol">{{</a><a id="9156" href="simple_essence.html#9156" class="Bound">_</a> <a id="9158" class="Symbol">:</a> <a id="9160" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="9169" href="simple_essence.html#9116" class="Bound">A</a><a id="9170" class="Symbol">}}</a>
        <a id="9181" class="Symbol">{{</a><a id="9183" href="simple_essence.html#9183" class="Bound">_</a> <a id="9185" class="Symbol">:</a> <a id="9187" href="simple_essence.html#7866" class="Record">VectorSpace</a> <a id="9199" href="simple_essence.html#9116" class="Bound">A</a><a id="9200" class="Symbol">}}</a>
        <a id="9211" class="Comment">-------------------------------------</a>
      <a id="9255" class="Symbol">→</a> <a id="9257" href="simple_essence.html#9116" class="Bound">A</a> <a id="9259" class="Symbol">→</a> <a id="9261" href="simple_essence.html#7120" class="Record">LinMap</a> <a id="9268" href="simple_essence.html#9116" class="Bound">A</a> <a id="9270" href="simple_essence.html#6194" class="Datatype">§</a>
<a id="9272" href="simple_essence.html#9107" class="Function">a⊸§←a</a> <a id="9278" class="Symbol">=</a> <a id="9280" class="Symbol">λ</a> <a id="9282" class="Symbol">{</a> <a id="9284" href="simple_essence.html#9284" class="Bound">a</a> <a id="9286" class="Symbol">→</a> <a id="9288" href="simple_essence.html#7297" class="InductiveConstructor">mkLM</a> <a id="9293" class="Symbol">(</a><a id="9294" href="simple_essence.html#9284" class="Bound">a</a> <a id="9296" href="simple_essence.html#8111" class="Field Operator">·_</a><a id="9298" class="Symbol">)</a> <a id="9300" href="simple_essence.html#8189" class="Field">·-distrib-⊕</a> <a id="9312" href="simple_essence.html#8321" class="Field">·-comm-⊛</a> <a id="9321" class="Symbol">}</a>

<a id="9324" class="Comment">-- Danger, Will Robinson!</a>
<a id="9350" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9362" href="simple_essence.html#9362" class="Postulate">x·z≡y·z→x≡y</a> <a id="9374" class="Symbol">:</a> <a id="9376" class="Symbol">{</a><a id="9377" href="simple_essence.html#9377" class="Bound">A</a> <a id="9379" class="Symbol">:</a> <a id="9381" class="PrimitiveType">Set</a> <a id="9385" href="simple_essence.html#5580" class="Bound">a</a><a id="9386" class="Symbol">}</a>
                <a id="9404" class="Symbol">{{</a><a id="9406" href="simple_essence.html#9406" class="Bound">_</a> <a id="9408" class="Symbol">:</a> <a id="9410" href="simple_essence.html#6234" class="Record">Additive</a> <a id="9419" href="simple_essence.html#9377" class="Bound">A</a><a id="9420" class="Symbol">}}</a> <a id="9423" class="Symbol">{{</a><a id="9425" href="simple_essence.html#9425" class="Bound">_</a> <a id="9427" class="Symbol">:</a> <a id="9429" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="9438" href="simple_essence.html#9377" class="Bound">A</a><a id="9439" class="Symbol">}}</a> <a id="9442" class="Symbol">{{</a><a id="9444" href="simple_essence.html#9444" class="Bound">_</a> <a id="9446" class="Symbol">:</a> <a id="9448" href="simple_essence.html#7866" class="Record">VectorSpace</a> <a id="9460" href="simple_essence.html#9377" class="Bound">A</a><a id="9461" class="Symbol">}}</a>
                <a id="9480" class="Symbol">{</a><a id="9481" href="simple_essence.html#9481" class="Bound">x</a> <a id="9483" href="simple_essence.html#9483" class="Bound">y</a> <a id="9485" class="Symbol">:</a> <a id="9487" href="simple_essence.html#9377" class="Bound">A</a><a id="9488" class="Symbol">}</a>
              <a id="9504" class="Symbol">→</a> <a id="9506" class="Symbol">(∀</a> <a id="9509" class="Symbol">{</a><a id="9510" href="simple_essence.html#9510" class="Bound">z</a> <a id="9512" class="Symbol">:</a> <a id="9514" href="simple_essence.html#9377" class="Bound">A</a><a id="9515" class="Symbol">}</a> <a id="9517" class="Symbol">→</a> <a id="9519" href="simple_essence.html#9481" class="Bound">x</a> <a id="9521" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="9523" href="simple_essence.html#9510" class="Bound">z</a> <a id="9525" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9527" href="simple_essence.html#9483" class="Bound">y</a> <a id="9529" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="9531" href="simple_essence.html#9510" class="Bound">z</a><a id="9532" class="Symbol">)</a>
                <a id="9550" class="Comment">-----------------------------------------------------------</a>
              <a id="9624" class="Symbol">→</a> <a id="9626" href="simple_essence.html#9481" class="Bound">x</a> <a id="9628" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9630" href="simple_essence.html#9483" class="Bound">y</a>
<a id="9632" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9692" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9759" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9790" href="simple_essence.html#9790" class="Function">a⊸§↔a</a> <a id="9796" class="Symbol">:</a> <a id="9798" class="Symbol">{</a><a id="9799" href="simple_essence.html#9799" class="Bound">A</a> <a id="9801" class="Symbol">:</a> <a id="9803" class="PrimitiveType">Set</a> <a id="9807" href="simple_essence.html#5580" class="Bound">a</a><a id="9808" class="Symbol">}</a>
        <a id="9818" class="Symbol">{{</a><a id="9820" href="simple_essence.html#9820" class="Bound">_</a> <a id="9822" class="Symbol">:</a> <a id="9824" href="simple_essence.html#6234" class="Record">Additive</a> <a id="9833" href="simple_essence.html#9799" class="Bound">A</a><a id="9834" class="Symbol">}}</a> <a id="9837" class="Symbol">{{</a><a id="9839" href="simple_essence.html#9839" class="Bound">_</a> <a id="9841" class="Symbol">:</a> <a id="9843" href="simple_essence.html#6848" class="Record">Scalable</a> <a id="9852" href="simple_essence.html#9799" class="Bound">A</a><a id="9853" class="Symbol">}}</a>
        <a id="9864" class="Symbol">{{</a><a id="9866" href="simple_essence.html#9866" class="Bound">_</a> <a id="9868" class="Symbol">:</a> <a id="9870" href="simple_essence.html#7866" class="Record">VectorSpace</a> <a id="9882" href="simple_essence.html#9799" class="Bound">A</a><a id="9883" class="Symbol">}}</a>
        <a id="9894" class="Comment">-------------------------------------</a>
      <a id="9938" class="Symbol">→</a> <a id="9940" class="Symbol">(</a><a id="9941" href="simple_essence.html#7120" class="Record">LinMap</a> <a id="9948" href="simple_essence.html#9799" class="Bound">A</a> <a id="9950" href="simple_essence.html#6194" class="Datatype">§</a><a id="9951" class="Symbol">)</a> <a id="9953" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9955" href="simple_essence.html#9799" class="Bound">A</a>
<a id="9957" href="simple_essence.html#9790" class="Function">a⊸§↔a</a> <a id="9963" class="Symbol">{</a><a id="9964" href="simple_essence.html#9964" class="Bound">A</a><a id="9965" class="Symbol">}</a> <a id="9967" class="Symbol">=</a>
  <a id="9971" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9975" class="Symbol">{</a><a id="9976" class="Argument">f</a> <a id="9978" class="Symbol">=</a> <a id="9980" href="simple_essence.html#8865" class="Function">a⊸§→a</a><a id="9985" class="Symbol">}</a> <a id="9987" class="Symbol">{</a><a id="9988" class="Argument">f⁻¹</a> <a id="9992" class="Symbol">=</a> <a id="9994" href="simple_essence.html#9107" class="Function">a⊸§←a</a><a id="9999" class="Symbol">}</a>
      <a id="10007" class="Symbol">(</a> <a id="10009" class="Symbol">(λ</a> <a id="10012" class="Symbol">{</a><a id="10013" href="simple_essence.html#10013" class="Bound">x</a> <a id="10015" class="Symbol">→</a> <a id="10017" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10041" href="simple_essence.html#8865" class="Function">a⊸§→a</a> <a id="10047" class="Symbol">(</a><a id="10048" href="simple_essence.html#9107" class="Function">a⊸§←a</a> <a id="10054" href="simple_essence.html#10013" class="Bound">x</a><a id="10055" class="Symbol">)</a>
                <a id="10073" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10095" href="simple_essence.html#8865" class="Function">a⊸§→a</a> <a id="10101" class="Symbol">(</a><a id="10102" href="simple_essence.html#7297" class="InductiveConstructor">mkLM</a> <a id="10107" class="Symbol">(</a><a id="10108" href="simple_essence.html#10013" class="Bound">x</a> <a id="10110" href="simple_essence.html#8111" class="Field Operator">·_</a><a id="10112" class="Symbol">)</a> <a id="10114" href="simple_essence.html#8189" class="Field">·-distrib-⊕</a> <a id="10126" href="simple_essence.html#8321" class="Field">·-comm-⊛</a><a id="10134" class="Symbol">)</a>
                <a id="10152" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10174" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10180" class="Symbol">(λ</a> <a id="10183" href="simple_essence.html#10183" class="Bound">acc</a> <a id="10187" href="simple_essence.html#10187" class="Bound">v</a> <a id="10189" class="Symbol">→</a> <a id="10191" href="simple_essence.html#10183" class="Bound">acc</a> <a id="10195" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="10197" class="Symbol">(</a><a id="10198" href="simple_essence.html#10013" class="Bound">x</a> <a id="10200" href="simple_essence.html#8111" class="Field Operator">·</a> <a id="10202" href="simple_essence.html#10187" class="Bound">v</a><a id="10203" class="Symbol">)</a> <a id="10205" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="10207" href="simple_essence.html#10187" class="Bound">v</a><a id="10208" class="Symbol">)</a> <a id="10210" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="10214" href="simple_essence.html#8086" class="Field">basisSet</a>
                <a id="10239" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10242" href="simple_essence.html#9362" class="Postulate">x·z≡y·z→x≡y</a> <a id="10254" class="Symbol">(</a><a id="10255" href="simple_essence.html#8589" class="Field">orthonormal</a> <a id="10267" class="Symbol">{</a><a id="10268" class="Argument">f</a> <a id="10270" class="Symbol">=</a> <a id="10272" class="Symbol">(</a><a id="10273" href="simple_essence.html#10013" class="Bound">x</a> <a id="10275" href="simple_essence.html#8111" class="Field Operator">·_</a><a id="10277" class="Symbol">)})</a> <a id="10281" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10301" href="simple_essence.html#10013" class="Bound">x</a>
                <a id="10319" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10320" class="Symbol">})</a>
      <a id="10329" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10331" class="Symbol">λ</a> <a id="10333" class="Symbol">{</a><a id="10334" href="simple_essence.html#10334" class="Bound">lm</a> <a id="10337" class="Symbol">→</a> <a id="10339" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10363" href="simple_essence.html#9107" class="Function">a⊸§←a</a> <a id="10369" class="Symbol">(</a><a id="10370" href="simple_essence.html#8865" class="Function">a⊸§→a</a> <a id="10376" href="simple_essence.html#10334" class="Bound">lm</a><a id="10378" class="Symbol">)</a>
                <a id="10396" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10418" href="simple_essence.html#9107" class="Function">a⊸§←a</a> <a id="10424" class="Symbol">(</a><a id="10425" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10431" class="Symbol">(λ</a> <a id="10434" href="simple_essence.html#10434" class="Bound">acc</a> <a id="10438" href="simple_essence.html#10438" class="Bound">v</a> <a id="10440" class="Symbol">→</a> <a id="10442" href="simple_essence.html#10434" class="Bound">acc</a> <a id="10446" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="10448" class="Symbol">(</a><a id="10449" href="simple_essence.html#7314" class="Field">LinMap.f</a> <a id="10458" href="simple_essence.html#10334" class="Bound">lm</a> <a id="10461" href="simple_essence.html#10438" class="Bound">v</a><a id="10462" class="Symbol">)</a> <a id="10464" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="10466" href="simple_essence.html#10438" class="Bound">v</a><a id="10467" class="Symbol">)</a> <a id="10469" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="10473" href="simple_essence.html#8086" class="Field">basisSet</a><a id="10481" class="Symbol">)</a>
                <a id="10499" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10521" href="simple_essence.html#7297" class="InductiveConstructor">mkLM</a> <a id="10526" class="Symbol">((</a><a id="10528" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10534" class="Symbol">(λ</a> <a id="10537" href="simple_essence.html#10537" class="Bound">acc</a> <a id="10541" href="simple_essence.html#10541" class="Bound">v</a> <a id="10543" class="Symbol">→</a> <a id="10545" href="simple_essence.html#10537" class="Bound">acc</a> <a id="10549" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="10551" class="Symbol">(</a><a id="10552" href="simple_essence.html#7314" class="Field">LinMap.f</a> <a id="10561" href="simple_essence.html#10334" class="Bound">lm</a> <a id="10564" href="simple_essence.html#10541" class="Bound">v</a><a id="10565" class="Symbol">)</a> <a id="10567" href="simple_essence.html#6961" class="Field Operator">⊛</a> <a id="10569" href="simple_essence.html#10541" class="Bound">v</a><a id="10570" class="Symbol">)</a> <a id="10572" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="10576" href="simple_essence.html#8086" class="Field">basisSet</a><a id="10584" class="Symbol">)</a><a id="10585" href="simple_essence.html#8111" class="Field Operator">·_</a><a id="10587" class="Symbol">)</a>
                       <a id="10612" href="simple_essence.html#8189" class="Field">·-distrib-⊕</a> <a id="10624" href="simple_essence.html#8321" class="Field">·-comm-⊛</a>
                <a id="10649" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10652" href="simple_essence.html#7632" class="Postulate">⊸≡</a> <a id="10655" class="Symbol">(</a> <a id="10657" href="simple_essence.html#6113" class="Postulate">extensionality</a>
                          <a id="10698" class="Symbol">(</a> <a id="10700" class="Symbol">λ</a> <a id="10702" href="simple_essence.html#10702" class="Bound">x</a> <a id="10704" class="Symbol">→</a> <a id="10706" href="simple_essence.html#8589" class="Field">orthonormal</a> <a id="10718" class="Symbol">{</a><a id="10719" class="Argument">f</a> <a id="10721" class="Symbol">=</a> <a id="10723" href="simple_essence.html#7314" class="Field">LinMap.f</a> <a id="10732" href="simple_essence.html#10334" class="Bound">lm</a><a id="10734" class="Symbol">}</a> <a id="10736" class="Symbol">{</a><a id="10737" class="Argument">x</a> <a id="10739" class="Symbol">=</a> <a id="10741" href="simple_essence.html#10702" class="Bound">x</a><a id="10742" class="Symbol">}</a> <a id="10744" class="Symbol">)</a>
                      <a id="10768" class="Symbol">)</a>
                 <a id="10787" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10807" href="simple_essence.html#10334" class="Bound">lm</a>
                <a id="10826" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10827" class="Symbol">}</a>
      <a id="10835" class="Symbol">)</a>

<a id="10838" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10921" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10983" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="11077" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="11140" class="Comment">--</a>
<a id="11143" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="11166" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="11215" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="11248" class="Comment">--         -------------------------------------</a>
<a id="11297" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11325" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>