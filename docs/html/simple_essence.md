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
<a id="6499" class="Keyword">open</a> <a id="6504" href="simple_essence.html#6234" class="Module">Additive</a> <a id="6513" class="Symbol">⦃</a> <a id="6515" class="Symbol">...</a> <a id="6519" class="Symbol">⦄</a>
<a id="6521" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6532" href="simple_essence.html#6532" class="Function">AdditiveScalar</a> <a id="6547" class="Symbol">:</a> <a id="6549" href="simple_essence.html#6234" class="Record">Additive</a> <a id="6558" href="simple_essence.html#6194" class="Datatype">§</a>
  <a id="6562" href="simple_essence.html#6532" class="Function">AdditiveScalar</a> <a id="6577" class="Symbol">=</a> <a id="6579" class="Keyword">record</a>
    <a id="6590" class="Symbol">{</a> <a id="6592" href="simple_essence.html#6347" class="Field">id⊕</a>  <a id="6597" class="Symbol">=</a> <a id="6599" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6601" class="Number">0.0</a>
    <a id="6609" class="Symbol">;</a> <a id="6611" href="simple_essence.html#6360" class="Field Operator">_⊕_</a>  <a id="6616" class="Symbol">=</a> <a id="6618" class="Symbol">λ</a> <a id="6620" class="Symbol">{(</a><a id="6622" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6624" href="simple_essence.html#6624" class="Bound">x</a><a id="6625" class="Symbol">)</a> <a id="6627" class="Symbol">(</a><a id="6628" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6630" href="simple_essence.html#6630" class="Bound">y</a><a id="6631" class="Symbol">)</a> <a id="6633" class="Symbol">→</a> <a id="6635" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6637" class="Symbol">(</a><a id="6638" href="simple_essence.html#6624" class="Bound">x</a> <a id="6640" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6642" href="simple_essence.html#6630" class="Bound">y</a><a id="6643" class="Symbol">)}</a>
    <a id="6650" class="Symbol">;</a> <a id="6652" href="simple_essence.html#6381" class="Field">id-⊕</a> <a id="6657" class="Symbol">=</a> <a id="6659" class="Symbol">λ</a> <a id="6661" class="Symbol">{</a> <a id="6663" class="Symbol">(</a><a id="6664" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6666" href="simple_essence.html#6666" class="Bound">x</a><a id="6667" class="Symbol">)</a> <a id="6669" class="Symbol">→</a> <a id="6671" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6704" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6706" class="Symbol">(</a><a id="6707" class="Number">0.0</a> <a id="6711" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6713" href="simple_essence.html#6666" class="Bound">x</a><a id="6714" class="Symbol">)</a>
                         <a id="6741" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6744" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6749" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6751" href="simple_essence.html#6079" class="Postulate">id+</a> <a id="6755" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6784" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="6786" href="simple_essence.html#6666" class="Bound">x</a>
                         <a id="6813" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6830" class="Symbol">}</a>
    <a id="6836" class="Symbol">}</a>

<a id="6839" class="Keyword">record</a> <a id="Scalable"></a><a id="6846" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="6855" class="Symbol">(</a><a id="6856" href="simple_essence.html#6856" class="Bound">A</a> <a id="6858" class="Symbol">:</a> <a id="6860" class="PrimitiveType">Set</a> <a id="6864" href="simple_essence.html#5580" class="Bound">a</a><a id="6865" class="Symbol">)</a> <a id="6867" class="Symbol">:</a> <a id="6869" class="PrimitiveType">Set</a> <a id="6873" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="6875" class="Keyword">where</a>
  <a id="6883" class="Keyword">infixl</a> <a id="6890" class="Number">7</a> <a id="6892" href="simple_essence.html#6959" class="Field Operator">_⊛_</a>  <a id="6897" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6949" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6959" href="simple_essence.html#6959" class="Field Operator">_⊛_</a> <a id="6963" class="Symbol">:</a> <a id="6965" href="simple_essence.html#6194" class="Datatype">§</a> <a id="6967" class="Symbol">→</a> <a id="6969" href="simple_essence.html#6856" class="Bound">A</a> <a id="6971" class="Symbol">→</a> <a id="6973" href="simple_essence.html#6856" class="Bound">A</a>
<a id="6975" class="Keyword">open</a> <a id="6980" href="simple_essence.html#6846" class="Module">Scalable</a> <a id="6989" class="Symbol">⦃</a> <a id="6991" class="Symbol">...</a> <a id="6995" class="Symbol">⦄</a>
<a id="6997" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="7008" href="simple_essence.html#7008" class="Function">ScalableScalar</a> <a id="7023" class="Symbol">:</a> <a id="7025" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="7034" href="simple_essence.html#6194" class="Datatype">§</a>
  <a id="7038" href="simple_essence.html#7008" class="Function">ScalableScalar</a> <a id="7053" class="Symbol">=</a> <a id="7055" class="Keyword">record</a>
    <a id="7066" class="Symbol">{</a> <a id="7068" href="simple_essence.html#6959" class="Field Operator">_⊛_</a> <a id="7072" class="Symbol">=</a> <a id="7074" class="Symbol">λ</a> <a id="7076" class="Symbol">{(</a><a id="7078" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="7080" href="simple_essence.html#7080" class="Bound">x</a><a id="7081" class="Symbol">)</a> <a id="7083" class="Symbol">(</a><a id="7084" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="7086" href="simple_essence.html#7086" class="Bound">y</a><a id="7087" class="Symbol">)</a> <a id="7089" class="Symbol">→</a> <a id="7091" href="simple_essence.html#6212" class="InductiveConstructor">S</a> <a id="7093" class="Symbol">(</a><a id="7094" href="simple_essence.html#7080" class="Bound">x</a> <a id="7096" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="7098" href="simple_essence.html#7086" class="Bound">y</a><a id="7099" class="Symbol">)}</a>
    <a id="7106" class="Symbol">}</a>

<a id="7109" class="Keyword">record</a> <a id="LinMap"></a><a id="7116" href="simple_essence.html#7116" class="Record">LinMap</a> <a id="7123" class="Symbol">(</a><a id="7124" href="simple_essence.html#7124" class="Bound">A</a> <a id="7126" class="Symbol">:</a> <a id="7128" class="PrimitiveType">Set</a> <a id="7132" href="simple_essence.html#5580" class="Bound">a</a><a id="7133" class="Symbol">)</a> <a id="7135" class="Symbol">(</a><a id="7136" href="simple_essence.html#7136" class="Bound">B</a> <a id="7138" class="Symbol">:</a> <a id="7140" class="PrimitiveType">Set</a> <a id="7144" href="simple_essence.html#5580" class="Bound">a</a><a id="7145" class="Symbol">)</a>
              <a id="7161" class="Symbol">⦃</a> <a id="7163" href="simple_essence.html#7163" class="Bound">_</a> <a id="7165" class="Symbol">:</a> <a id="7167" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7176" href="simple_essence.html#7124" class="Bound">A</a> <a id="7178" class="Symbol">⦄</a> <a id="7180" class="Symbol">⦃</a> <a id="7182" href="simple_essence.html#7182" class="Bound">_</a> <a id="7184" class="Symbol">:</a> <a id="7186" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7195" href="simple_essence.html#7136" class="Bound">B</a> <a id="7197" class="Symbol">⦄</a>
              <a id="7213" class="Symbol">⦃</a> <a id="7215" href="simple_essence.html#7215" class="Bound">_</a> <a id="7217" class="Symbol">:</a> <a id="7219" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="7228" href="simple_essence.html#7124" class="Bound">A</a> <a id="7230" class="Symbol">⦄</a> <a id="7232" class="Symbol">⦃</a> <a id="7234" href="simple_essence.html#7234" class="Bound">_</a> <a id="7236" class="Symbol">:</a> <a id="7238" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="7247" href="simple_essence.html#7136" class="Bound">B</a> <a id="7249" class="Symbol">⦄</a>
              <a id="7265" class="Symbol">:</a> <a id="7267" class="PrimitiveType">Set</a> <a id="7271" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="7273" class="Keyword">where</a>
  <a id="7281" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7293" href="simple_essence.html#7293" class="InductiveConstructor">mkLM</a>
  <a id="7300" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7310" href="simple_essence.html#7310" class="Field">f</a>      <a id="7317" class="Symbol">:</a> <a id="7319" href="simple_essence.html#7124" class="Bound">A</a> <a id="7321" class="Symbol">→</a> <a id="7323" href="simple_essence.html#7136" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7330" href="simple_essence.html#7330" class="Field">adds</a>   <a id="7337" class="Symbol">:</a> <a id="7339" class="Symbol">∀</a> <a id="7341" class="Symbol">{</a><a id="7342" href="simple_essence.html#7342" class="Bound">a</a> <a id="7344" href="simple_essence.html#7344" class="Bound">b</a> <a id="7346" class="Symbol">:</a> <a id="7348" href="simple_essence.html#7124" class="Bound">A</a><a id="7349" class="Symbol">}</a>
             <a id="7364" class="Comment">---------------------</a>
           <a id="7397" class="Symbol">→</a> <a id="7399" href="simple_essence.html#7310" class="Field">f</a> <a id="7401" class="Symbol">(</a><a id="7402" href="simple_essence.html#7342" class="Bound">a</a> <a id="7404" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="7406" href="simple_essence.html#7344" class="Bound">b</a><a id="7407" class="Symbol">)</a> <a id="7409" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7411" href="simple_essence.html#7310" class="Field">f</a> <a id="7413" href="simple_essence.html#7342" class="Bound">a</a> <a id="7415" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="7417" href="simple_essence.html#7310" class="Field">f</a> <a id="7419" href="simple_essence.html#7344" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7426" href="simple_essence.html#7426" class="Field">scales</a> <a id="7433" class="Symbol">:</a> <a id="7435" class="Symbol">∀</a> <a id="7437" class="Symbol">{</a><a id="7438" href="simple_essence.html#7438" class="Bound">s</a> <a id="7440" class="Symbol">:</a> <a id="7442" href="simple_essence.html#6194" class="Datatype">§</a><a id="7443" class="Symbol">}</a> <a id="7445" class="Symbol">{</a><a id="7446" href="simple_essence.html#7446" class="Bound">a</a> <a id="7448" class="Symbol">:</a> <a id="7450" href="simple_essence.html#7124" class="Bound">A</a><a id="7451" class="Symbol">}</a>
             <a id="7466" class="Comment">-------------------</a>
           <a id="7497" class="Symbol">→</a> <a id="7499" href="simple_essence.html#7310" class="Field">f</a> <a id="7501" class="Symbol">(</a><a id="7502" href="simple_essence.html#7438" class="Bound">s</a> <a id="7504" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="7506" href="simple_essence.html#7446" class="Bound">a</a><a id="7507" class="Symbol">)</a> <a id="7509" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7511" href="simple_essence.html#7438" class="Bound">s</a> <a id="7513" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="7515" href="simple_essence.html#7310" class="Field">f</a> <a id="7517" href="simple_essence.html#7446" class="Bound">a</a>
<a id="7519" class="Keyword">open</a> <a id="7524" href="simple_essence.html#7116" class="Module">LinMap</a> <a id="7531" class="Symbol">⦃</a> <a id="7533" class="Symbol">...</a> <a id="7537" class="Symbol">⦄</a>

<a id="7540" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7566" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7614" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7626" href="simple_essence.html#7626" class="Postulate">⊸≡</a> <a id="7629" class="Symbol">:</a> <a id="7631" class="Symbol">{</a><a id="7632" href="simple_essence.html#7632" class="Bound">A</a> <a id="7634" href="simple_essence.html#7634" class="Bound">B</a> <a id="7636" class="Symbol">:</a> <a id="7638" class="PrimitiveType">Set</a> <a id="7642" href="simple_essence.html#5580" class="Bound">a</a><a id="7643" class="Symbol">}</a>
       <a id="7652" class="Symbol">⦃</a> <a id="7654" href="simple_essence.html#7654" class="Bound">_</a> <a id="7656" class="Symbol">:</a> <a id="7658" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7667" href="simple_essence.html#7632" class="Bound">A</a> <a id="7669" class="Symbol">⦄</a> <a id="7671" class="Symbol">⦃</a> <a id="7673" href="simple_essence.html#7673" class="Bound">_</a> <a id="7675" class="Symbol">:</a> <a id="7677" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7686" href="simple_essence.html#7634" class="Bound">B</a> <a id="7688" class="Symbol">⦄</a>
       <a id="7697" class="Symbol">⦃</a> <a id="7699" href="simple_essence.html#7699" class="Bound">_</a> <a id="7701" class="Symbol">:</a> <a id="7703" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="7712" href="simple_essence.html#7632" class="Bound">A</a> <a id="7714" class="Symbol">⦄</a> <a id="7716" class="Symbol">⦃</a> <a id="7718" href="simple_essence.html#7718" class="Bound">_</a> <a id="7720" class="Symbol">:</a> <a id="7722" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="7731" href="simple_essence.html#7634" class="Bound">B</a> <a id="7733" class="Symbol">⦄</a>
       <a id="7742" class="Symbol">{</a><a id="7743" href="simple_essence.html#7743" class="Bound">lm₁</a> <a id="7747" href="simple_essence.html#7747" class="Bound">lm₂</a> <a id="7751" class="Symbol">:</a> <a id="7753" href="simple_essence.html#7116" class="Record">LinMap</a> <a id="7760" href="simple_essence.html#7632" class="Bound">A</a> <a id="7762" href="simple_essence.html#7634" class="Bound">B</a><a id="7763" class="Symbol">}</a>
     <a id="7770" class="Symbol">→</a> <a id="7772" href="simple_essence.html#7310" class="Field">LinMap.f</a> <a id="7781" href="simple_essence.html#7743" class="Bound">lm₁</a> <a id="7785" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7787" href="simple_essence.html#7310" class="Field">LinMap.f</a> <a id="7796" href="simple_essence.html#7747" class="Bound">lm₂</a>
       <a id="7807" class="Comment">---------------------------</a>
     <a id="7840" class="Symbol">→</a> <a id="7842" href="simple_essence.html#7743" class="Bound">lm₁</a> <a id="7846" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7848" href="simple_essence.html#7747" class="Bound">lm₂</a>

<a id="7853" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7860" href="simple_essence.html#7860" class="Record">VectorSpace</a> <a id="7872" class="Symbol">(</a><a id="7873" href="simple_essence.html#7873" class="Bound">A</a> <a id="7875" class="Symbol">:</a> <a id="7877" class="PrimitiveType">Set</a> <a id="7881" href="simple_essence.html#5580" class="Bound">a</a><a id="7882" class="Symbol">)</a>
                   <a id="7903" class="Symbol">⦃</a> <a id="7905" href="simple_essence.html#7905" class="Bound">_</a> <a id="7907" class="Symbol">:</a> <a id="7909" href="simple_essence.html#6234" class="Record">Additive</a> <a id="7918" href="simple_essence.html#7873" class="Bound">A</a> <a id="7920" class="Symbol">⦄</a> <a id="7922" class="Symbol">⦃</a> <a id="7924" href="simple_essence.html#7924" class="Bound">_</a> <a id="7926" class="Symbol">:</a> <a id="7928" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="7937" href="simple_essence.html#7873" class="Bound">A</a> <a id="7939" class="Symbol">⦄</a>
                   <a id="7960" class="Symbol">:</a> <a id="7962" class="PrimitiveType">Set</a> <a id="7966" href="simple_essence.html#6164" class="Function">ℓ</a> <a id="7968" class="Keyword">where</a>
  <a id="7976" class="Keyword">field</a>
    <a id="7986" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="8080" href="simple_essence.html#8080" class="Field">basisSet</a>    <a id="8092" class="Symbol">:</a> <a id="8094" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="8099" href="simple_essence.html#7873" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="8105" href="simple_essence.html#8105" class="Field Operator">_·_</a>         <a id="8117" class="Symbol">:</a> <a id="8119" href="simple_essence.html#7873" class="Bound">A</a> <a id="8121" class="Symbol">→</a> <a id="8123" href="simple_essence.html#7873" class="Bound">A</a> <a id="8125" class="Symbol">→</a> <a id="8127" href="simple_essence.html#6194" class="Datatype">§</a>
    <a id="8133" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="8183" href="simple_essence.html#8183" class="Field">·-distrib-⊕</a> <a id="8195" class="Symbol">:</a> <a id="8197" class="Symbol">∀</a> <a id="8199" class="Symbol">{</a><a id="8200" href="simple_essence.html#8200" class="Bound">a</a> <a id="8202" href="simple_essence.html#8202" class="Bound">b</a> <a id="8204" href="simple_essence.html#8204" class="Bound">c</a> <a id="8206" class="Symbol">:</a> <a id="8208" href="simple_essence.html#7873" class="Bound">A</a><a id="8209" class="Symbol">}</a>
                  <a id="8229" class="Comment">-------------------------------</a>
                <a id="8277" class="Symbol">→</a> <a id="8279" href="simple_essence.html#8200" class="Bound">a</a> <a id="8281" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="8283" class="Symbol">(</a><a id="8284" href="simple_essence.html#8202" class="Bound">b</a> <a id="8286" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="8288" href="simple_essence.html#8204" class="Bound">c</a><a id="8289" class="Symbol">)</a> <a id="8291" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8293" class="Symbol">(</a><a id="8294" href="simple_essence.html#8200" class="Bound">a</a> <a id="8296" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="8298" href="simple_essence.html#8202" class="Bound">b</a><a id="8299" class="Symbol">)</a> <a id="8301" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="8303" class="Symbol">(</a><a id="8304" href="simple_essence.html#8200" class="Bound">a</a> <a id="8306" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="8308" href="simple_essence.html#8204" class="Bound">c</a><a id="8309" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8315" href="simple_essence.html#8315" class="Field">·-comm-⊛</a>    <a id="8327" class="Symbol">:</a> <a id="8329" class="Symbol">∀</a> <a id="8331" class="Symbol">{</a><a id="8332" href="simple_essence.html#8332" class="Bound">s</a> <a id="8334" class="Symbol">:</a> <a id="8336" href="simple_essence.html#6194" class="Datatype">§</a><a id="8337" class="Symbol">}</a> <a id="8339" class="Symbol">{</a><a id="8340" href="simple_essence.html#8340" class="Bound">a</a> <a id="8342" href="simple_essence.html#8342" class="Bound">b</a> <a id="8344" class="Symbol">:</a> <a id="8346" href="simple_essence.html#7873" class="Bound">A</a><a id="8347" class="Symbol">}</a>
                  <a id="8367" class="Comment">-------------------------</a>
                <a id="8409" class="Symbol">→</a> <a id="8411" href="simple_essence.html#8340" class="Bound">a</a> <a id="8413" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="8415" class="Symbol">(</a><a id="8416" href="simple_essence.html#8332" class="Bound">s</a> <a id="8418" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="8420" href="simple_essence.html#8342" class="Bound">b</a><a id="8421" class="Symbol">)</a> <a id="8423" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8425" href="simple_essence.html#8332" class="Bound">s</a> <a id="8427" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="8429" class="Symbol">(</a><a id="8430" href="simple_essence.html#8340" class="Bound">a</a> <a id="8432" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="8434" href="simple_essence.html#8342" class="Bound">b</a><a id="8435" class="Symbol">)</a>
    <a id="8441" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8525" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8583" href="simple_essence.html#8583" class="Field">orthonormal</a> <a id="8595" class="Symbol">:</a> <a id="8597" class="Symbol">∀</a> <a id="8599" class="Symbol">{</a><a id="8600" href="simple_essence.html#8600" class="Bound">f</a> <a id="8602" class="Symbol">:</a> <a id="8604" href="simple_essence.html#7873" class="Bound">A</a> <a id="8606" class="Symbol">→</a> <a id="8608" href="simple_essence.html#6194" class="Datatype">§</a><a id="8609" class="Symbol">}</a>
                <a id="8627" class="Symbol">→</a> <a id="8629" class="Symbol">{</a><a id="8630" href="simple_essence.html#8630" class="Bound">x</a> <a id="8632" class="Symbol">:</a> <a id="8634" href="simple_essence.html#7873" class="Bound">A</a><a id="8635" class="Symbol">}</a>
                  <a id="8655" class="Comment">----------------------------------------------------------</a>
                <a id="8730" class="Symbol">→</a> <a id="8732" class="Symbol">(</a><a id="8733" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8739" class="Symbol">(λ</a> <a id="8742" href="simple_essence.html#8742" class="Bound">acc</a> <a id="8746" href="simple_essence.html#8746" class="Bound">v</a> <a id="8748" class="Symbol">→</a> <a id="8750" href="simple_essence.html#8742" class="Bound">acc</a> <a id="8754" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="8756" class="Symbol">(</a><a id="8757" href="simple_essence.html#8600" class="Bound">f</a> <a id="8759" href="simple_essence.html#8746" class="Bound">v</a><a id="8760" class="Symbol">)</a> <a id="8762" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="8764" href="simple_essence.html#8746" class="Bound">v</a><a id="8765" class="Symbol">)</a> <a id="8767" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="8771" href="simple_essence.html#8080" class="Field">basisSet</a><a id="8779" class="Symbol">)</a> <a id="8781" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="8783" href="simple_essence.html#8630" class="Bound">x</a> <a id="8785" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8787" href="simple_essence.html#8600" class="Bound">f</a> <a id="8789" href="simple_essence.html#8630" class="Bound">x</a>
<a id="8791" class="Keyword">open</a> <a id="8796" href="simple_essence.html#7860" class="Module">VectorSpace</a> <a id="8808" class="Symbol">⦃</a> <a id="8810" class="Symbol">...</a> <a id="8814" class="Symbol">⦄</a>

<a id="8817" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8857" href="simple_essence.html#8857" class="Function">a⊸§→a</a> <a id="8863" class="Symbol">:</a> <a id="8865" class="Symbol">{</a><a id="8866" href="simple_essence.html#8866" class="Bound">A</a> <a id="8868" class="Symbol">:</a> <a id="8870" class="PrimitiveType">Set</a> <a id="8874" href="simple_essence.html#5580" class="Bound">a</a><a id="8875" class="Symbol">}</a>
        <a id="8885" class="Symbol">⦃</a> <a id="8887" href="simple_essence.html#8887" class="Bound">_</a> <a id="8889" class="Symbol">:</a> <a id="8891" href="simple_essence.html#6234" class="Record">Additive</a> <a id="8900" href="simple_essence.html#8866" class="Bound">A</a> <a id="8902" class="Symbol">⦄</a> <a id="8904" class="Symbol">⦃</a> <a id="8906" href="simple_essence.html#8906" class="Bound">_</a> <a id="8908" class="Symbol">:</a> <a id="8910" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="8919" href="simple_essence.html#8866" class="Bound">A</a> <a id="8921" class="Symbol">⦄</a>
        <a id="8931" class="Symbol">⦃</a> <a id="8933" href="simple_essence.html#8933" class="Bound">_</a> <a id="8935" class="Symbol">:</a> <a id="8937" href="simple_essence.html#7860" class="Record">VectorSpace</a> <a id="8949" href="simple_essence.html#8866" class="Bound">A</a> <a id="8951" class="Symbol">⦄</a>
        <a id="8961" class="Comment">-------------------------------------</a>
      <a id="9005" class="Symbol">→</a> <a id="9007" href="simple_essence.html#7116" class="Record">LinMap</a> <a id="9014" href="simple_essence.html#8866" class="Bound">A</a> <a id="9016" href="simple_essence.html#6194" class="Datatype">§</a> <a id="9018" class="Symbol">→</a> <a id="9020" href="simple_essence.html#8866" class="Bound">A</a>
<a id="9022" href="simple_essence.html#8857" class="Function">a⊸§→a</a> <a id="9028" class="Symbol">=</a> <a id="9030" class="Symbol">λ</a> <a id="9032" class="Symbol">{</a> <a id="9034" href="simple_essence.html#9034" class="Bound">lm</a> <a id="9037" class="Symbol">→</a> <a id="9039" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="9045" class="Symbol">(λ</a> <a id="9048" href="simple_essence.html#9048" class="Bound">acc</a> <a id="9052" href="simple_essence.html#9052" class="Bound">v</a> <a id="9054" class="Symbol">→</a> <a id="9056" href="simple_essence.html#9048" class="Bound">acc</a> <a id="9060" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="9062" class="Symbol">(</a><a id="9063" href="simple_essence.html#7310" class="Field">LinMap.f</a> <a id="9072" href="simple_essence.html#9034" class="Bound">lm</a> <a id="9075" href="simple_essence.html#9052" class="Bound">v</a><a id="9076" class="Symbol">)</a> <a id="9078" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="9080" href="simple_essence.html#9052" class="Bound">v</a><a id="9081" class="Symbol">)</a> <a id="9083" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="9087" href="simple_essence.html#8080" class="Field">basisSet</a> <a id="9096" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="9099" href="simple_essence.html#9099" class="Function">a⊸§←a</a> <a id="9105" class="Symbol">:</a> <a id="9107" class="Symbol">{</a><a id="9108" href="simple_essence.html#9108" class="Bound">A</a> <a id="9110" class="Symbol">:</a> <a id="9112" class="PrimitiveType">Set</a> <a id="9116" href="simple_essence.html#5580" class="Bound">a</a><a id="9117" class="Symbol">}</a>
        <a id="9127" class="Symbol">⦃</a> <a id="9129" href="simple_essence.html#9129" class="Bound">_</a> <a id="9131" class="Symbol">:</a> <a id="9133" href="simple_essence.html#6234" class="Record">Additive</a> <a id="9142" href="simple_essence.html#9108" class="Bound">A</a> <a id="9144" class="Symbol">⦄</a> <a id="9146" class="Symbol">⦃</a> <a id="9148" href="simple_essence.html#9148" class="Bound">_</a> <a id="9150" class="Symbol">:</a> <a id="9152" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="9161" href="simple_essence.html#9108" class="Bound">A</a> <a id="9163" class="Symbol">⦄</a>
        <a id="9173" class="Symbol">⦃</a> <a id="9175" href="simple_essence.html#9175" class="Bound">_</a> <a id="9177" class="Symbol">:</a> <a id="9179" href="simple_essence.html#7860" class="Record">VectorSpace</a> <a id="9191" href="simple_essence.html#9108" class="Bound">A</a> <a id="9193" class="Symbol">⦄</a>
        <a id="9203" class="Comment">-------------------------------------</a>
      <a id="9247" class="Symbol">→</a> <a id="9249" href="simple_essence.html#9108" class="Bound">A</a> <a id="9251" class="Symbol">→</a> <a id="9253" href="simple_essence.html#7116" class="Record">LinMap</a> <a id="9260" href="simple_essence.html#9108" class="Bound">A</a> <a id="9262" href="simple_essence.html#6194" class="Datatype">§</a>
<a id="9264" href="simple_essence.html#9099" class="Function">a⊸§←a</a> <a id="9270" class="Symbol">=</a> <a id="9272" class="Symbol">λ</a> <a id="9274" class="Symbol">{</a> <a id="9276" href="simple_essence.html#9276" class="Bound">a</a> <a id="9278" class="Symbol">→</a> <a id="9280" href="simple_essence.html#7293" class="InductiveConstructor">mkLM</a> <a id="9285" class="Symbol">(</a><a id="9286" href="simple_essence.html#9276" class="Bound">a</a> <a id="9288" href="simple_essence.html#8105" class="Field Operator">·_</a><a id="9290" class="Symbol">)</a> <a id="9292" href="simple_essence.html#8183" class="Field">·-distrib-⊕</a> <a id="9304" href="simple_essence.html#8315" class="Field">·-comm-⊛</a> <a id="9313" class="Symbol">}</a>

<a id="9316" class="Comment">-- Danger, Will Robinson!</a>
<a id="9342" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9354" href="simple_essence.html#9354" class="Postulate">x·z≡y·z→x≡y</a> <a id="9366" class="Symbol">:</a> <a id="9368" class="Symbol">{</a><a id="9369" href="simple_essence.html#9369" class="Bound">A</a> <a id="9371" class="Symbol">:</a> <a id="9373" class="PrimitiveType">Set</a> <a id="9377" href="simple_essence.html#5580" class="Bound">a</a><a id="9378" class="Symbol">}</a>
                <a id="9396" class="Symbol">⦃</a> <a id="9398" href="simple_essence.html#9398" class="Bound">_</a> <a id="9400" class="Symbol">:</a> <a id="9402" href="simple_essence.html#6234" class="Record">Additive</a> <a id="9411" href="simple_essence.html#9369" class="Bound">A</a> <a id="9413" class="Symbol">⦄</a> <a id="9415" class="Symbol">⦃</a> <a id="9417" href="simple_essence.html#9417" class="Bound">_</a> <a id="9419" class="Symbol">:</a> <a id="9421" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="9430" href="simple_essence.html#9369" class="Bound">A</a> <a id="9432" class="Symbol">⦄</a> <a id="9434" class="Symbol">⦃</a> <a id="9436" href="simple_essence.html#9436" class="Bound">_</a> <a id="9438" class="Symbol">:</a> <a id="9440" href="simple_essence.html#7860" class="Record">VectorSpace</a> <a id="9452" href="simple_essence.html#9369" class="Bound">A</a> <a id="9454" class="Symbol">⦄</a>
                <a id="9472" class="Symbol">{</a><a id="9473" href="simple_essence.html#9473" class="Bound">x</a> <a id="9475" href="simple_essence.html#9475" class="Bound">y</a> <a id="9477" class="Symbol">:</a> <a id="9479" href="simple_essence.html#9369" class="Bound">A</a><a id="9480" class="Symbol">}</a>
              <a id="9496" class="Symbol">→</a> <a id="9498" class="Symbol">(∀</a> <a id="9501" class="Symbol">{</a><a id="9502" href="simple_essence.html#9502" class="Bound">z</a> <a id="9504" class="Symbol">:</a> <a id="9506" href="simple_essence.html#9369" class="Bound">A</a><a id="9507" class="Symbol">}</a> <a id="9509" class="Symbol">→</a> <a id="9511" href="simple_essence.html#9473" class="Bound">x</a> <a id="9513" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="9515" href="simple_essence.html#9502" class="Bound">z</a> <a id="9517" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9519" href="simple_essence.html#9475" class="Bound">y</a> <a id="9521" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="9523" href="simple_essence.html#9502" class="Bound">z</a><a id="9524" class="Symbol">)</a>
                <a id="9542" class="Comment">-----------------------------------------------------------</a>
              <a id="9616" class="Symbol">→</a> <a id="9618" href="simple_essence.html#9473" class="Bound">x</a> <a id="9620" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9622" href="simple_essence.html#9475" class="Bound">y</a>
<a id="9624" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9684" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9751" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9782" href="simple_essence.html#9782" class="Function">a⊸§↔a</a> <a id="9788" class="Symbol">:</a> <a id="9790" class="Symbol">{</a><a id="9791" href="simple_essence.html#9791" class="Bound">A</a> <a id="9793" class="Symbol">:</a> <a id="9795" class="PrimitiveType">Set</a> <a id="9799" href="simple_essence.html#5580" class="Bound">a</a><a id="9800" class="Symbol">}</a>
        <a id="9810" class="Symbol">⦃</a> <a id="9812" href="simple_essence.html#9812" class="Bound">_</a> <a id="9814" class="Symbol">:</a> <a id="9816" href="simple_essence.html#6234" class="Record">Additive</a> <a id="9825" href="simple_essence.html#9791" class="Bound">A</a> <a id="9827" class="Symbol">⦄</a> <a id="9829" class="Symbol">⦃</a> <a id="9831" href="simple_essence.html#9831" class="Bound">_</a> <a id="9833" class="Symbol">:</a> <a id="9835" href="simple_essence.html#6846" class="Record">Scalable</a> <a id="9844" href="simple_essence.html#9791" class="Bound">A</a> <a id="9846" class="Symbol">⦄</a>
        <a id="9856" class="Symbol">⦃</a> <a id="9858" href="simple_essence.html#9858" class="Bound">_</a> <a id="9860" class="Symbol">:</a> <a id="9862" href="simple_essence.html#7860" class="Record">VectorSpace</a> <a id="9874" href="simple_essence.html#9791" class="Bound">A</a> <a id="9876" class="Symbol">⦄</a>
        <a id="9886" class="Comment">-------------------------------------</a>
      <a id="9930" class="Symbol">→</a> <a id="9932" class="Symbol">(</a><a id="9933" href="simple_essence.html#7116" class="Record">LinMap</a> <a id="9940" href="simple_essence.html#9791" class="Bound">A</a> <a id="9942" href="simple_essence.html#6194" class="Datatype">§</a><a id="9943" class="Symbol">)</a> <a id="9945" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9947" href="simple_essence.html#9791" class="Bound">A</a>
<a id="9949" href="simple_essence.html#9782" class="Function">a⊸§↔a</a> <a id="9955" class="Symbol">{</a><a id="9956" href="simple_essence.html#9956" class="Bound">A</a><a id="9957" class="Symbol">}</a> <a id="9959" class="Symbol">=</a>
  <a id="9963" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9967" class="Symbol">{</a><a id="9968" class="Argument">f</a> <a id="9970" class="Symbol">=</a> <a id="9972" href="simple_essence.html#8857" class="Function">a⊸§→a</a><a id="9977" class="Symbol">}</a> <a id="9979" class="Symbol">{</a><a id="9980" class="Argument">f⁻¹</a> <a id="9984" class="Symbol">=</a> <a id="9986" href="simple_essence.html#9099" class="Function">a⊸§←a</a><a id="9991" class="Symbol">}</a>
      <a id="9999" class="Symbol">(</a> <a id="10001" class="Symbol">(λ</a> <a id="10004" class="Symbol">{</a><a id="10005" href="simple_essence.html#10005" class="Bound">x</a> <a id="10007" class="Symbol">→</a> <a id="10009" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10033" href="simple_essence.html#8857" class="Function">a⊸§→a</a> <a id="10039" class="Symbol">(</a><a id="10040" href="simple_essence.html#9099" class="Function">a⊸§←a</a> <a id="10046" href="simple_essence.html#10005" class="Bound">x</a><a id="10047" class="Symbol">)</a>
                <a id="10065" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10087" href="simple_essence.html#8857" class="Function">a⊸§→a</a> <a id="10093" class="Symbol">(</a><a id="10094" href="simple_essence.html#7293" class="InductiveConstructor">mkLM</a> <a id="10099" class="Symbol">(</a><a id="10100" href="simple_essence.html#10005" class="Bound">x</a> <a id="10102" href="simple_essence.html#8105" class="Field Operator">·_</a><a id="10104" class="Symbol">)</a> <a id="10106" href="simple_essence.html#8183" class="Field">·-distrib-⊕</a> <a id="10118" href="simple_essence.html#8315" class="Field">·-comm-⊛</a><a id="10126" class="Symbol">)</a>
                <a id="10144" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10166" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10172" class="Symbol">(λ</a> <a id="10175" href="simple_essence.html#10175" class="Bound">acc</a> <a id="10179" href="simple_essence.html#10179" class="Bound">v</a> <a id="10181" class="Symbol">→</a> <a id="10183" href="simple_essence.html#10175" class="Bound">acc</a> <a id="10187" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="10189" class="Symbol">(</a><a id="10190" href="simple_essence.html#10005" class="Bound">x</a> <a id="10192" href="simple_essence.html#8105" class="Field Operator">·</a> <a id="10194" href="simple_essence.html#10179" class="Bound">v</a><a id="10195" class="Symbol">)</a> <a id="10197" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="10199" href="simple_essence.html#10179" class="Bound">v</a><a id="10200" class="Symbol">)</a> <a id="10202" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="10206" href="simple_essence.html#8080" class="Field">basisSet</a>
                <a id="10231" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10234" href="simple_essence.html#9354" class="Postulate">x·z≡y·z→x≡y</a> <a id="10246" class="Symbol">(</a><a id="10247" href="simple_essence.html#8583" class="Field">orthonormal</a> <a id="10259" class="Symbol">{</a><a id="10260" class="Argument">f</a> <a id="10262" class="Symbol">=</a> <a id="10264" class="Symbol">(</a><a id="10265" href="simple_essence.html#10005" class="Bound">x</a> <a id="10267" href="simple_essence.html#8105" class="Field Operator">·_</a><a id="10269" class="Symbol">)})</a> <a id="10273" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10293" href="simple_essence.html#10005" class="Bound">x</a>
                <a id="10311" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10312" class="Symbol">})</a>
      <a id="10321" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10323" class="Symbol">λ</a> <a id="10325" class="Symbol">{</a><a id="10326" href="simple_essence.html#10326" class="Bound">lm</a> <a id="10329" class="Symbol">→</a> <a id="10331" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10355" href="simple_essence.html#9099" class="Function">a⊸§←a</a> <a id="10361" class="Symbol">(</a><a id="10362" href="simple_essence.html#8857" class="Function">a⊸§→a</a> <a id="10368" href="simple_essence.html#10326" class="Bound">lm</a><a id="10370" class="Symbol">)</a>
                <a id="10388" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10410" href="simple_essence.html#9099" class="Function">a⊸§←a</a> <a id="10416" class="Symbol">(</a><a id="10417" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10423" class="Symbol">(λ</a> <a id="10426" href="simple_essence.html#10426" class="Bound">acc</a> <a id="10430" href="simple_essence.html#10430" class="Bound">v</a> <a id="10432" class="Symbol">→</a> <a id="10434" href="simple_essence.html#10426" class="Bound">acc</a> <a id="10438" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="10440" class="Symbol">(</a><a id="10441" href="simple_essence.html#7310" class="Field">LinMap.f</a> <a id="10450" href="simple_essence.html#10326" class="Bound">lm</a> <a id="10453" href="simple_essence.html#10430" class="Bound">v</a><a id="10454" class="Symbol">)</a> <a id="10456" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="10458" href="simple_essence.html#10430" class="Bound">v</a><a id="10459" class="Symbol">)</a> <a id="10461" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="10465" href="simple_essence.html#8080" class="Field">basisSet</a><a id="10473" class="Symbol">)</a>
                <a id="10491" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10513" href="simple_essence.html#7293" class="InductiveConstructor">mkLM</a> <a id="10518" class="Symbol">((</a><a id="10520" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10526" class="Symbol">(λ</a> <a id="10529" href="simple_essence.html#10529" class="Bound">acc</a> <a id="10533" href="simple_essence.html#10533" class="Bound">v</a> <a id="10535" class="Symbol">→</a> <a id="10537" href="simple_essence.html#10529" class="Bound">acc</a> <a id="10541" href="simple_essence.html#6360" class="Field Operator">⊕</a> <a id="10543" class="Symbol">(</a><a id="10544" href="simple_essence.html#7310" class="Field">LinMap.f</a> <a id="10553" href="simple_essence.html#10326" class="Bound">lm</a> <a id="10556" href="simple_essence.html#10533" class="Bound">v</a><a id="10557" class="Symbol">)</a> <a id="10559" href="simple_essence.html#6959" class="Field Operator">⊛</a> <a id="10561" href="simple_essence.html#10533" class="Bound">v</a><a id="10562" class="Symbol">)</a> <a id="10564" href="simple_essence.html#6347" class="Field">id⊕</a> <a id="10568" href="simple_essence.html#8080" class="Field">basisSet</a><a id="10576" class="Symbol">)</a><a id="10577" href="simple_essence.html#8105" class="Field Operator">·_</a><a id="10579" class="Symbol">)</a>
                       <a id="10604" href="simple_essence.html#8183" class="Field">·-distrib-⊕</a> <a id="10616" href="simple_essence.html#8315" class="Field">·-comm-⊛</a>
                <a id="10641" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10644" href="simple_essence.html#7626" class="Postulate">⊸≡</a> <a id="10647" class="Symbol">(</a> <a id="10649" href="simple_essence.html#6113" class="Postulate">extensionality</a>
                          <a id="10690" class="Symbol">(</a> <a id="10692" class="Symbol">λ</a> <a id="10694" href="simple_essence.html#10694" class="Bound">x</a> <a id="10696" class="Symbol">→</a> <a id="10698" href="simple_essence.html#8583" class="Field">orthonormal</a> <a id="10710" class="Symbol">{</a><a id="10711" class="Argument">f</a> <a id="10713" class="Symbol">=</a> <a id="10715" href="simple_essence.html#7310" class="Field">LinMap.f</a> <a id="10724" href="simple_essence.html#10326" class="Bound">lm</a><a id="10726" class="Symbol">}</a> <a id="10728" class="Symbol">{</a><a id="10729" class="Argument">x</a> <a id="10731" class="Symbol">=</a> <a id="10733" href="simple_essence.html#10694" class="Bound">x</a><a id="10734" class="Symbol">}</a> <a id="10736" class="Symbol">)</a>
                      <a id="10760" class="Symbol">)</a>
                 <a id="10779" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10799" href="simple_essence.html#10326" class="Bound">lm</a>
                <a id="10818" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10819" class="Symbol">}</a>
      <a id="10827" class="Symbol">)</a>

<a id="10830" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10913" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10975" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="11069" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="11132" class="Comment">--</a>
<a id="11135" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="11158" class="Comment">--         ⦃_ : Additive A⦄ ⦃_ : Scalable A⦄</a>
<a id="11203" class="Comment">--         ⦃_ : VectorSpace A⦄</a>
<a id="11234" class="Comment">--         -------------------------------------</a>
<a id="11283" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11311" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>