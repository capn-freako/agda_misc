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

<pre class="Agda"><a id="5484" class="Keyword">module</a> <a id="5491" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5506" class="Symbol">{</a><a id="5507" href="simple_essence.html#5507" class="Bound">s</a> <a id="5509" href="simple_essence.html#5509" class="Bound">a</a> <a id="5511" href="simple_essence.html#5511" class="Bound">b</a><a id="5512" class="Symbol">}</a> <a id="5514" class="Keyword">where</a>

<a id="5521" class="Keyword">open</a> <a id="5526" class="Keyword">import</a> <a id="5533" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5552" class="Keyword">open</a> <a id="5557" class="Keyword">import</a> <a id="5564" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5599" class="Keyword">using</a> <a id="5605" class="Symbol">(</a><a id="5606" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5620" class="Symbol">)</a>
<a id="5622" class="Keyword">open</a> <a id="5627" class="Keyword">import</a> <a id="5634" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5645" class="Keyword">open</a> <a id="5650" class="Keyword">import</a> <a id="5657" href="Data.List.html" class="Module">Data.List</a>
<a id="5667" class="Keyword">open</a> <a id="5672" class="Keyword">import</a> <a id="5679" href="Function.html" class="Module">Function</a> <a id="5688" class="Keyword">using</a> <a id="5694" class="Symbol">(</a><a id="5695" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5698" class="Symbol">;</a> <a id="5700" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5703" class="Symbol">;</a> <a id="5705" href="Function.Base.html#615" class="Function">id</a><a id="5707" class="Symbol">)</a>
<a id="5709" class="Keyword">open</a> <a id="5714" class="Keyword">import</a> <a id="5721" href="Level.html" class="Module">Level</a> <a id="5727" class="Keyword">using</a> <a id="5733" class="Symbol">(</a><a id="5734" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5739" class="Symbol">;</a> <a id="5741" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5744" class="Symbol">)</a>

<a id="5747" class="Keyword">import</a> <a id="5754" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5792" class="Symbol">as</a> <a id="5795" class="Module">Eq</a>
<a id="5798" class="Keyword">open</a> <a id="5803" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5806" class="Keyword">using</a> <a id="5812" class="Symbol">(</a><a id="5813" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5816" class="Symbol">;</a> <a id="5818" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5822" class="Symbol">;</a> <a id="5824" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5829" class="Symbol">;</a> <a id="5831" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5834" class="Symbol">;</a> <a id="5836" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5840" class="Symbol">;</a> <a id="5842" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5847" class="Symbol">;</a> <a id="5849" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5857" class="Symbol">;</a> <a id="5859" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5864" class="Symbol">)</a>
<a id="5866" class="Keyword">open</a> <a id="5871" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5886" class="Keyword">using</a> <a id="5892" class="Symbol">(</a><a id="5893" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5899" class="Symbol">;</a> <a id="5901" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5906" class="Symbol">;</a> <a id="5908" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5914" class="Symbol">;</a> <a id="5916" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5918" class="Symbol">)</a>

<a id="5921" class="Keyword">postulate</a>
  <a id="5933" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="6008" href="simple_essence.html#6008" class="Postulate">id+</a> <a id="6012" class="Symbol">:</a> <a id="6014" class="Symbol">{</a><a id="6015" href="simple_essence.html#6015" class="Bound">x</a> <a id="6017" class="Symbol">:</a> <a id="6019" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="6024" class="Symbol">}</a> <a id="6026" class="Symbol">→</a> <a id="6028" class="Number">0.0</a> <a id="6032" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6034" href="simple_essence.html#6015" class="Bound">x</a> <a id="6036" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6038" href="simple_essence.html#6015" class="Bound">x</a>
  <a id="extensionality"></a><a id="6042" href="simple_essence.html#6042" class="Postulate">extensionality</a> <a id="6057" class="Symbol">:</a> <a id="6059" class="Symbol">∀</a> <a id="6061" class="Symbol">{</a><a id="6062" href="simple_essence.html#6062" class="Bound">ℓ₁</a> <a id="6065" href="simple_essence.html#6065" class="Bound">ℓ₂</a><a id="6067" class="Symbol">}</a> <a id="6069" class="Symbol">→</a> <a id="6071" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="6086" href="simple_essence.html#6062" class="Bound">ℓ₁</a> <a id="6089" href="simple_essence.html#6065" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="6093" href="simple_essence.html#6093" class="Function">ℓ</a> <a id="6095" class="Symbol">:</a> <a id="6097" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="6103" href="simple_essence.html#6093" class="Function">ℓ</a> <a id="6105" class="Symbol">=</a> <a id="6107" href="simple_essence.html#5507" class="Bound">s</a> <a id="6109" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6111" href="simple_essence.html#5509" class="Bound">a</a> <a id="6113" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6115" href="simple_essence.html#5511" class="Bound">b</a>

<a id="6118" class="Keyword">data</a> <a id="§"></a><a id="6123" href="simple_essence.html#6123" class="Datatype">§</a> <a id="6125" class="Symbol">:</a> <a id="6127" class="PrimitiveType">Set</a> <a id="6131" href="simple_essence.html#5509" class="Bound">a</a> <a id="6133" class="Keyword">where</a>
  <a id="§.S"></a><a id="6141" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6143" class="Symbol">:</a> <a id="6145" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="6151" class="Symbol">→</a> <a id="6153" href="simple_essence.html#6123" class="Datatype">§</a>

<a id="6156" class="Keyword">record</a> <a id="Additive"></a><a id="6163" href="simple_essence.html#6163" class="Record">Additive</a> <a id="6172" class="Symbol">(</a><a id="6173" href="simple_essence.html#6173" class="Bound">A</a> <a id="6175" class="Symbol">:</a> <a id="6177" class="PrimitiveType">Set</a> <a id="6181" href="simple_essence.html#5509" class="Bound">a</a><a id="6182" class="Symbol">)</a> <a id="6184" class="Symbol">:</a> <a id="6186" class="PrimitiveType">Set</a> <a id="6190" href="simple_essence.html#6093" class="Function">ℓ</a> <a id="6192" class="Keyword">where</a>
  <a id="6200" class="Keyword">infixl</a> <a id="6207" class="Number">6</a> <a id="6209" href="simple_essence.html#6289" class="Field Operator">_⊕_</a>  <a id="6214" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6266" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6276" href="simple_essence.html#6276" class="Field">id⊕</a>  <a id="6281" class="Symbol">:</a> <a id="6283" href="simple_essence.html#6173" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6289" href="simple_essence.html#6289" class="Field Operator">_⊕_</a>  <a id="6294" class="Symbol">:</a> <a id="6296" href="simple_essence.html#6173" class="Bound">A</a> <a id="6298" class="Symbol">→</a> <a id="6300" href="simple_essence.html#6173" class="Bound">A</a> <a id="6302" class="Symbol">→</a> <a id="6304" href="simple_essence.html#6173" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6310" href="simple_essence.html#6310" class="Field">id-⊕</a> <a id="6315" class="Symbol">:</a> <a id="6317" class="Symbol">(</a><a id="6318" href="simple_essence.html#6318" class="Bound">a</a> <a id="6320" class="Symbol">:</a> <a id="6322" href="simple_essence.html#6173" class="Bound">A</a><a id="6323" class="Symbol">)</a>
           <a id="6336" class="Comment">-----------</a>
         <a id="6357" class="Symbol">→</a> <a id="6359" href="simple_essence.html#6276" class="Field">id⊕</a> <a id="6363" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="6365" href="simple_essence.html#6318" class="Bound">a</a> <a id="6367" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6369" href="simple_essence.html#6318" class="Bound">a</a>
    <a id="6375" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6428" class="Keyword">open</a> <a id="6433" href="simple_essence.html#6163" class="Module">Additive</a> <a id="6442" class="Symbol">{{</a> <a id="6445" class="Symbol">...</a> <a id="6449" class="Symbol">}}</a>
<a id="6452" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6463" href="simple_essence.html#6463" class="Function">AdditiveScalar</a> <a id="6478" class="Symbol">:</a> <a id="6480" href="simple_essence.html#6163" class="Record">Additive</a> <a id="6489" href="simple_essence.html#6123" class="Datatype">§</a>
  <a id="6493" href="simple_essence.html#6463" class="Function">AdditiveScalar</a> <a id="6508" class="Symbol">=</a> <a id="6510" class="Keyword">record</a>
    <a id="6521" class="Symbol">{</a> <a id="6523" href="simple_essence.html#6276" class="Field">id⊕</a>  <a id="6528" class="Symbol">=</a> <a id="6530" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6532" class="Number">0.0</a>
    <a id="6540" class="Symbol">;</a> <a id="6542" href="simple_essence.html#6289" class="Field Operator">_⊕_</a>  <a id="6547" class="Symbol">=</a> <a id="6549" class="Symbol">λ</a> <a id="6551" class="Symbol">{(</a><a id="6553" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6555" href="simple_essence.html#6555" class="Bound">x</a><a id="6556" class="Symbol">)</a> <a id="6558" class="Symbol">(</a><a id="6559" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6561" href="simple_essence.html#6561" class="Bound">y</a><a id="6562" class="Symbol">)</a> <a id="6564" class="Symbol">→</a> <a id="6566" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6568" class="Symbol">(</a><a id="6569" href="simple_essence.html#6555" class="Bound">x</a> <a id="6571" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6573" href="simple_essence.html#6561" class="Bound">y</a><a id="6574" class="Symbol">)}</a>
    <a id="6581" class="Symbol">;</a> <a id="6583" href="simple_essence.html#6310" class="Field">id-⊕</a> <a id="6588" class="Symbol">=</a> <a id="6590" class="Symbol">λ</a> <a id="6592" class="Symbol">{</a> <a id="6594" class="Symbol">(</a><a id="6595" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6597" href="simple_essence.html#6597" class="Bound">x</a><a id="6598" class="Symbol">)</a> <a id="6600" class="Symbol">→</a> <a id="6602" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6635" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6637" class="Symbol">(</a><a id="6638" class="Number">0.0</a> <a id="6642" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6644" href="simple_essence.html#6597" class="Bound">x</a><a id="6645" class="Symbol">)</a>
                         <a id="6672" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6675" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6680" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6682" href="simple_essence.html#6008" class="Postulate">id+</a> <a id="6686" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6715" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="6717" href="simple_essence.html#6597" class="Bound">x</a>
                         <a id="6744" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6761" class="Symbol">}</a>
    <a id="6767" class="Symbol">}</a>

<a id="6770" class="Keyword">record</a> <a id="Scalable"></a><a id="6777" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="6786" class="Symbol">(</a><a id="6787" href="simple_essence.html#6787" class="Bound">A</a> <a id="6789" class="Symbol">:</a> <a id="6791" class="PrimitiveType">Set</a> <a id="6795" href="simple_essence.html#5509" class="Bound">a</a><a id="6796" class="Symbol">)</a> <a id="6798" class="Symbol">:</a> <a id="6800" class="PrimitiveType">Set</a> <a id="6804" href="simple_essence.html#6093" class="Function">ℓ</a> <a id="6806" class="Keyword">where</a>
  <a id="6814" class="Keyword">infixl</a> <a id="6821" class="Number">7</a> <a id="6823" href="simple_essence.html#6890" class="Field Operator">_⊛_</a>  <a id="6828" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6880" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6890" href="simple_essence.html#6890" class="Field Operator">_⊛_</a> <a id="6894" class="Symbol">:</a> <a id="6896" href="simple_essence.html#6123" class="Datatype">§</a> <a id="6898" class="Symbol">→</a> <a id="6900" href="simple_essence.html#6787" class="Bound">A</a> <a id="6902" class="Symbol">→</a> <a id="6904" href="simple_essence.html#6787" class="Bound">A</a>
<a id="6906" class="Keyword">open</a> <a id="6911" href="simple_essence.html#6777" class="Module">Scalable</a> <a id="6920" class="Symbol">{{</a> <a id="6923" class="Symbol">...</a> <a id="6927" class="Symbol">}}</a>
<a id="6930" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="6941" href="simple_essence.html#6941" class="Function">ScalableScalar</a> <a id="6956" class="Symbol">:</a> <a id="6958" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="6967" href="simple_essence.html#6123" class="Datatype">§</a>
  <a id="6971" href="simple_essence.html#6941" class="Function">ScalableScalar</a> <a id="6986" class="Symbol">=</a> <a id="6988" class="Keyword">record</a>
    <a id="6999" class="Symbol">{</a> <a id="7001" href="simple_essence.html#6890" class="Field Operator">_⊛_</a> <a id="7005" class="Symbol">=</a> <a id="7007" class="Symbol">λ</a> <a id="7009" class="Symbol">{(</a><a id="7011" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="7013" href="simple_essence.html#7013" class="Bound">x</a><a id="7014" class="Symbol">)</a> <a id="7016" class="Symbol">(</a><a id="7017" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="7019" href="simple_essence.html#7019" class="Bound">y</a><a id="7020" class="Symbol">)</a> <a id="7022" class="Symbol">→</a> <a id="7024" href="simple_essence.html#6141" class="InductiveConstructor">S</a> <a id="7026" class="Symbol">(</a><a id="7027" href="simple_essence.html#7013" class="Bound">x</a> <a id="7029" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="7031" href="simple_essence.html#7019" class="Bound">y</a><a id="7032" class="Symbol">)}</a>
    <a id="7039" class="Symbol">}</a>

<a id="7042" class="Keyword">record</a> <a id="LinMap"></a><a id="7049" href="simple_essence.html#7049" class="Record">LinMap</a> <a id="7056" class="Symbol">(</a><a id="7057" href="simple_essence.html#7057" class="Bound">A</a> <a id="7059" class="Symbol">:</a> <a id="7061" class="PrimitiveType">Set</a> <a id="7065" href="simple_essence.html#5509" class="Bound">a</a><a id="7066" class="Symbol">)</a> <a id="7068" class="Symbol">(</a><a id="7069" href="simple_essence.html#7069" class="Bound">B</a> <a id="7071" class="Symbol">:</a> <a id="7073" class="PrimitiveType">Set</a> <a id="7077" href="simple_essence.html#5509" class="Bound">a</a><a id="7078" class="Symbol">)</a>
              <a id="7094" class="Symbol">{{</a><a id="7096" href="simple_essence.html#7096" class="Bound">_</a> <a id="7098" class="Symbol">:</a> <a id="7100" href="simple_essence.html#6163" class="Record">Additive</a> <a id="7109" href="simple_essence.html#7057" class="Bound">A</a><a id="7110" class="Symbol">}}</a> <a id="7113" class="Symbol">{{</a><a id="7115" href="simple_essence.html#7115" class="Bound">_</a> <a id="7117" class="Symbol">:</a> <a id="7119" href="simple_essence.html#6163" class="Record">Additive</a> <a id="7128" href="simple_essence.html#7069" class="Bound">B</a><a id="7129" class="Symbol">}}</a>
              <a id="7146" class="Symbol">{{</a><a id="7148" href="simple_essence.html#7148" class="Bound">_</a> <a id="7150" class="Symbol">:</a> <a id="7152" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="7161" href="simple_essence.html#7057" class="Bound">A</a><a id="7162" class="Symbol">}}</a> <a id="7165" class="Symbol">{{</a><a id="7167" href="simple_essence.html#7167" class="Bound">_</a> <a id="7169" class="Symbol">:</a> <a id="7171" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="7180" href="simple_essence.html#7069" class="Bound">B</a><a id="7181" class="Symbol">}}</a>
              <a id="7198" class="Symbol">:</a> <a id="7200" class="PrimitiveType">Set</a> <a id="7204" href="simple_essence.html#6093" class="Function">ℓ</a> <a id="7206" class="Keyword">where</a>
  <a id="7214" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7226" href="simple_essence.html#7226" class="InductiveConstructor">mkLM</a>
  <a id="7233" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7243" href="simple_essence.html#7243" class="Field">f</a>      <a id="7250" class="Symbol">:</a> <a id="7252" href="simple_essence.html#7057" class="Bound">A</a> <a id="7254" class="Symbol">→</a> <a id="7256" href="simple_essence.html#7069" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7263" href="simple_essence.html#7263" class="Field">adds</a>   <a id="7270" class="Symbol">:</a> <a id="7272" class="Symbol">∀</a> <a id="7274" class="Symbol">{</a><a id="7275" href="simple_essence.html#7275" class="Bound">a</a> <a id="7277" href="simple_essence.html#7277" class="Bound">b</a> <a id="7279" class="Symbol">:</a> <a id="7281" href="simple_essence.html#7057" class="Bound">A</a><a id="7282" class="Symbol">}</a>
             <a id="7297" class="Comment">---------------------</a>
           <a id="7330" class="Symbol">→</a> <a id="7332" href="simple_essence.html#7243" class="Field">f</a> <a id="7334" class="Symbol">(</a><a id="7335" href="simple_essence.html#7275" class="Bound">a</a> <a id="7337" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="7339" href="simple_essence.html#7277" class="Bound">b</a><a id="7340" class="Symbol">)</a> <a id="7342" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7344" href="simple_essence.html#7243" class="Field">f</a> <a id="7346" href="simple_essence.html#7275" class="Bound">a</a> <a id="7348" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="7350" href="simple_essence.html#7243" class="Field">f</a> <a id="7352" href="simple_essence.html#7277" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7359" href="simple_essence.html#7359" class="Field">scales</a> <a id="7366" class="Symbol">:</a> <a id="7368" class="Symbol">∀</a> <a id="7370" class="Symbol">{</a><a id="7371" href="simple_essence.html#7371" class="Bound">s</a> <a id="7373" class="Symbol">:</a> <a id="7375" href="simple_essence.html#6123" class="Datatype">§</a><a id="7376" class="Symbol">}</a> <a id="7378" class="Symbol">{</a><a id="7379" href="simple_essence.html#7379" class="Bound">a</a> <a id="7381" class="Symbol">:</a> <a id="7383" href="simple_essence.html#7057" class="Bound">A</a><a id="7384" class="Symbol">}</a>
             <a id="7399" class="Comment">-------------------</a>
           <a id="7430" class="Symbol">→</a> <a id="7432" href="simple_essence.html#7243" class="Field">f</a> <a id="7434" class="Symbol">(</a><a id="7435" href="simple_essence.html#7371" class="Bound">s</a> <a id="7437" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="7439" href="simple_essence.html#7379" class="Bound">a</a><a id="7440" class="Symbol">)</a> <a id="7442" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7444" href="simple_essence.html#7371" class="Bound">s</a> <a id="7446" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="7448" href="simple_essence.html#7243" class="Field">f</a> <a id="7450" href="simple_essence.html#7379" class="Bound">a</a>
<a id="7452" class="Keyword">open</a> <a id="7457" href="simple_essence.html#7049" class="Module">LinMap</a> <a id="7464" class="Symbol">{{</a> <a id="7467" class="Symbol">...</a> <a id="7471" class="Symbol">}}</a>

<a id="7475" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7501" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7549" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7561" href="simple_essence.html#7561" class="Postulate">⊸≡</a> <a id="7564" class="Symbol">:</a> <a id="7566" class="Symbol">{</a><a id="7567" href="simple_essence.html#7567" class="Bound">A</a> <a id="7569" href="simple_essence.html#7569" class="Bound">B</a> <a id="7571" class="Symbol">:</a> <a id="7573" class="PrimitiveType">Set</a> <a id="7577" href="simple_essence.html#5509" class="Bound">a</a><a id="7578" class="Symbol">}</a>
       <a id="7587" class="Symbol">{{</a><a id="7589" href="simple_essence.html#7589" class="Bound">_</a> <a id="7591" class="Symbol">:</a> <a id="7593" href="simple_essence.html#6163" class="Record">Additive</a> <a id="7602" href="simple_essence.html#7567" class="Bound">A</a><a id="7603" class="Symbol">}}</a> <a id="7606" class="Symbol">{{</a><a id="7608" href="simple_essence.html#7608" class="Bound">_</a> <a id="7610" class="Symbol">:</a> <a id="7612" href="simple_essence.html#6163" class="Record">Additive</a> <a id="7621" href="simple_essence.html#7569" class="Bound">B</a><a id="7622" class="Symbol">}}</a>
       <a id="7632" class="Symbol">{{</a><a id="7634" href="simple_essence.html#7634" class="Bound">_</a> <a id="7636" class="Symbol">:</a> <a id="7638" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="7647" href="simple_essence.html#7567" class="Bound">A</a><a id="7648" class="Symbol">}}</a> <a id="7651" class="Symbol">{{</a><a id="7653" href="simple_essence.html#7653" class="Bound">_</a> <a id="7655" class="Symbol">:</a> <a id="7657" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="7666" href="simple_essence.html#7569" class="Bound">B</a><a id="7667" class="Symbol">}}</a>
       <a id="7677" class="Symbol">{</a><a id="7678" href="simple_essence.html#7678" class="Bound">lm₁</a> <a id="7682" href="simple_essence.html#7682" class="Bound">lm₂</a> <a id="7686" class="Symbol">:</a> <a id="7688" href="simple_essence.html#7049" class="Record">LinMap</a> <a id="7695" href="simple_essence.html#7567" class="Bound">A</a> <a id="7697" href="simple_essence.html#7569" class="Bound">B</a><a id="7698" class="Symbol">}</a>
     <a id="7705" class="Symbol">→</a> <a id="7707" href="simple_essence.html#7243" class="Field">LinMap.f</a> <a id="7716" href="simple_essence.html#7678" class="Bound">lm₁</a> <a id="7720" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7722" href="simple_essence.html#7243" class="Field">LinMap.f</a> <a id="7731" href="simple_essence.html#7682" class="Bound">lm₂</a>
       <a id="7742" class="Comment">---------------------------</a>
     <a id="7775" class="Symbol">→</a> <a id="7777" href="simple_essence.html#7678" class="Bound">lm₁</a> <a id="7781" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7783" href="simple_essence.html#7682" class="Bound">lm₂</a>

<a id="7788" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7795" href="simple_essence.html#7795" class="Record">VectorSpace</a> <a id="7807" class="Symbol">(</a><a id="7808" href="simple_essence.html#7808" class="Bound">A</a> <a id="7810" class="Symbol">:</a> <a id="7812" class="PrimitiveType">Set</a> <a id="7816" href="simple_essence.html#5509" class="Bound">a</a><a id="7817" class="Symbol">)</a>
                   <a id="7838" class="Symbol">{{</a><a id="7840" href="simple_essence.html#7840" class="Bound">_</a> <a id="7842" class="Symbol">:</a> <a id="7844" href="simple_essence.html#6163" class="Record">Additive</a> <a id="7853" href="simple_essence.html#7808" class="Bound">A</a><a id="7854" class="Symbol">}}</a> <a id="7857" class="Symbol">{{</a><a id="7859" href="simple_essence.html#7859" class="Bound">_</a> <a id="7861" class="Symbol">:</a> <a id="7863" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="7872" href="simple_essence.html#7808" class="Bound">A</a><a id="7873" class="Symbol">}}</a>
                   <a id="7895" class="Symbol">:</a> <a id="7897" class="PrimitiveType">Set</a> <a id="7901" href="simple_essence.html#6093" class="Function">ℓ</a> <a id="7903" class="Keyword">where</a>
  <a id="7911" class="Keyword">field</a>
    <a id="7921" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="8015" href="simple_essence.html#8015" class="Field">basisSet</a>    <a id="8027" class="Symbol">:</a> <a id="8029" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="8034" href="simple_essence.html#7808" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="8040" href="simple_essence.html#8040" class="Field Operator">_·_</a>         <a id="8052" class="Symbol">:</a> <a id="8054" href="simple_essence.html#7808" class="Bound">A</a> <a id="8056" class="Symbol">→</a> <a id="8058" href="simple_essence.html#7808" class="Bound">A</a> <a id="8060" class="Symbol">→</a> <a id="8062" href="simple_essence.html#6123" class="Datatype">§</a>
    <a id="8068" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="8118" href="simple_essence.html#8118" class="Field">·-distrib-⊕</a> <a id="8130" class="Symbol">:</a> <a id="8132" class="Symbol">∀</a> <a id="8134" class="Symbol">{</a><a id="8135" href="simple_essence.html#8135" class="Bound">a</a> <a id="8137" href="simple_essence.html#8137" class="Bound">b</a> <a id="8139" href="simple_essence.html#8139" class="Bound">c</a> <a id="8141" class="Symbol">:</a> <a id="8143" href="simple_essence.html#7808" class="Bound">A</a><a id="8144" class="Symbol">}</a>
                  <a id="8164" class="Comment">-------------------------------</a>
                <a id="8212" class="Symbol">→</a> <a id="8214" href="simple_essence.html#8135" class="Bound">a</a> <a id="8216" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="8218" class="Symbol">(</a><a id="8219" href="simple_essence.html#8137" class="Bound">b</a> <a id="8221" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="8223" href="simple_essence.html#8139" class="Bound">c</a><a id="8224" class="Symbol">)</a> <a id="8226" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8228" class="Symbol">(</a><a id="8229" href="simple_essence.html#8135" class="Bound">a</a> <a id="8231" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="8233" href="simple_essence.html#8137" class="Bound">b</a><a id="8234" class="Symbol">)</a> <a id="8236" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="8238" class="Symbol">(</a><a id="8239" href="simple_essence.html#8135" class="Bound">a</a> <a id="8241" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="8243" href="simple_essence.html#8139" class="Bound">c</a><a id="8244" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8250" href="simple_essence.html#8250" class="Field">·-comm-⊛</a>    <a id="8262" class="Symbol">:</a> <a id="8264" class="Symbol">∀</a> <a id="8266" class="Symbol">{</a><a id="8267" href="simple_essence.html#8267" class="Bound">s</a> <a id="8269" class="Symbol">:</a> <a id="8271" href="simple_essence.html#6123" class="Datatype">§</a><a id="8272" class="Symbol">}</a> <a id="8274" class="Symbol">{</a><a id="8275" href="simple_essence.html#8275" class="Bound">a</a> <a id="8277" href="simple_essence.html#8277" class="Bound">b</a> <a id="8279" class="Symbol">:</a> <a id="8281" href="simple_essence.html#7808" class="Bound">A</a><a id="8282" class="Symbol">}</a>
                  <a id="8302" class="Comment">-------------------------</a>
                <a id="8344" class="Symbol">→</a> <a id="8346" href="simple_essence.html#8275" class="Bound">a</a> <a id="8348" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="8350" class="Symbol">(</a><a id="8351" href="simple_essence.html#8267" class="Bound">s</a> <a id="8353" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="8355" href="simple_essence.html#8277" class="Bound">b</a><a id="8356" class="Symbol">)</a> <a id="8358" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8360" href="simple_essence.html#8267" class="Bound">s</a> <a id="8362" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="8364" class="Symbol">(</a><a id="8365" href="simple_essence.html#8275" class="Bound">a</a> <a id="8367" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="8369" href="simple_essence.html#8277" class="Bound">b</a><a id="8370" class="Symbol">)</a>
    <a id="8376" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8460" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8518" href="simple_essence.html#8518" class="Field">orthonormal</a> <a id="8530" class="Symbol">:</a> <a id="8532" class="Symbol">∀</a> <a id="8534" class="Symbol">{</a><a id="8535" href="simple_essence.html#8535" class="Bound">f</a> <a id="8537" class="Symbol">:</a> <a id="8539" href="simple_essence.html#7808" class="Bound">A</a> <a id="8541" class="Symbol">→</a> <a id="8543" href="simple_essence.html#6123" class="Datatype">§</a><a id="8544" class="Symbol">}</a>
                <a id="8562" class="Symbol">→</a> <a id="8564" class="Symbol">{</a><a id="8565" href="simple_essence.html#8565" class="Bound">x</a> <a id="8567" class="Symbol">:</a> <a id="8569" href="simple_essence.html#7808" class="Bound">A</a><a id="8570" class="Symbol">}</a>
                  <a id="8590" class="Comment">----------------------------------------------------------</a>
                <a id="8665" class="Symbol">→</a> <a id="8667" class="Symbol">(</a><a id="8668" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8674" class="Symbol">(λ</a> <a id="8677" href="simple_essence.html#8677" class="Bound">acc</a> <a id="8681" href="simple_essence.html#8681" class="Bound">v</a> <a id="8683" class="Symbol">→</a> <a id="8685" href="simple_essence.html#8677" class="Bound">acc</a> <a id="8689" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="8691" class="Symbol">(</a><a id="8692" href="simple_essence.html#8535" class="Bound">f</a> <a id="8694" href="simple_essence.html#8681" class="Bound">v</a><a id="8695" class="Symbol">)</a> <a id="8697" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="8699" href="simple_essence.html#8681" class="Bound">v</a><a id="8700" class="Symbol">)</a> <a id="8702" href="simple_essence.html#6276" class="Field">id⊕</a> <a id="8706" href="simple_essence.html#8015" class="Field">basisSet</a><a id="8714" class="Symbol">)</a> <a id="8716" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="8718" href="simple_essence.html#8565" class="Bound">x</a> <a id="8720" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8722" href="simple_essence.html#8535" class="Bound">f</a> <a id="8724" href="simple_essence.html#8565" class="Bound">x</a>
<a id="8726" class="Keyword">open</a> <a id="8731" href="simple_essence.html#7795" class="Module">VectorSpace</a> <a id="8743" class="Symbol">{{</a> <a id="8746" class="Symbol">...</a> <a id="8750" class="Symbol">}}</a>

<a id="8754" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8794" href="simple_essence.html#8794" class="Function">a⊸§→a</a> <a id="8800" class="Symbol">:</a> <a id="8802" class="Symbol">{</a><a id="8803" href="simple_essence.html#8803" class="Bound">A</a> <a id="8805" class="Symbol">:</a> <a id="8807" class="PrimitiveType">Set</a> <a id="8811" href="simple_essence.html#5509" class="Bound">a</a><a id="8812" class="Symbol">}</a>
        <a id="8822" class="Symbol">{{</a><a id="8824" href="simple_essence.html#8824" class="Bound">_</a> <a id="8826" class="Symbol">:</a> <a id="8828" href="simple_essence.html#6163" class="Record">Additive</a> <a id="8837" href="simple_essence.html#8803" class="Bound">A</a><a id="8838" class="Symbol">}}</a> <a id="8841" class="Symbol">{{</a><a id="8843" href="simple_essence.html#8843" class="Bound">_</a> <a id="8845" class="Symbol">:</a> <a id="8847" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="8856" href="simple_essence.html#8803" class="Bound">A</a><a id="8857" class="Symbol">}}</a>
        <a id="8868" class="Symbol">{{</a><a id="8870" href="simple_essence.html#8870" class="Bound">_</a> <a id="8872" class="Symbol">:</a> <a id="8874" href="simple_essence.html#7795" class="Record">VectorSpace</a> <a id="8886" href="simple_essence.html#8803" class="Bound">A</a><a id="8887" class="Symbol">}}</a>
        <a id="8898" class="Comment">-------------------------------------</a>
      <a id="8942" class="Symbol">→</a> <a id="8944" href="simple_essence.html#7049" class="Record">LinMap</a> <a id="8951" href="simple_essence.html#8803" class="Bound">A</a> <a id="8953" href="simple_essence.html#6123" class="Datatype">§</a> <a id="8955" class="Symbol">→</a> <a id="8957" href="simple_essence.html#8803" class="Bound">A</a>
<a id="8959" href="simple_essence.html#8794" class="Function">a⊸§→a</a> <a id="8965" class="Symbol">=</a> <a id="8967" class="Symbol">λ</a> <a id="8969" class="Symbol">{</a> <a id="8971" href="simple_essence.html#8971" class="Bound">lm</a> <a id="8974" class="Symbol">→</a> <a id="8976" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8982" class="Symbol">(λ</a> <a id="8985" href="simple_essence.html#8985" class="Bound">acc</a> <a id="8989" href="simple_essence.html#8989" class="Bound">v</a> <a id="8991" class="Symbol">→</a> <a id="8993" href="simple_essence.html#8985" class="Bound">acc</a> <a id="8997" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="8999" class="Symbol">(</a><a id="9000" href="simple_essence.html#7243" class="Field">LinMap.f</a> <a id="9009" href="simple_essence.html#8971" class="Bound">lm</a> <a id="9012" href="simple_essence.html#8989" class="Bound">v</a><a id="9013" class="Symbol">)</a> <a id="9015" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="9017" href="simple_essence.html#8989" class="Bound">v</a><a id="9018" class="Symbol">)</a> <a id="9020" href="simple_essence.html#6276" class="Field">id⊕</a> <a id="9024" href="simple_essence.html#8015" class="Field">basisSet</a> <a id="9033" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="9036" href="simple_essence.html#9036" class="Function">a⊸§←a</a> <a id="9042" class="Symbol">:</a> <a id="9044" class="Symbol">{</a><a id="9045" href="simple_essence.html#9045" class="Bound">A</a> <a id="9047" class="Symbol">:</a> <a id="9049" class="PrimitiveType">Set</a> <a id="9053" href="simple_essence.html#5509" class="Bound">a</a><a id="9054" class="Symbol">}</a>
        <a id="9064" class="Symbol">{{</a><a id="9066" href="simple_essence.html#9066" class="Bound">_</a> <a id="9068" class="Symbol">:</a> <a id="9070" href="simple_essence.html#6163" class="Record">Additive</a> <a id="9079" href="simple_essence.html#9045" class="Bound">A</a><a id="9080" class="Symbol">}}</a> <a id="9083" class="Symbol">{{</a><a id="9085" href="simple_essence.html#9085" class="Bound">_</a> <a id="9087" class="Symbol">:</a> <a id="9089" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="9098" href="simple_essence.html#9045" class="Bound">A</a><a id="9099" class="Symbol">}}</a>
        <a id="9110" class="Symbol">{{</a><a id="9112" href="simple_essence.html#9112" class="Bound">_</a> <a id="9114" class="Symbol">:</a> <a id="9116" href="simple_essence.html#7795" class="Record">VectorSpace</a> <a id="9128" href="simple_essence.html#9045" class="Bound">A</a><a id="9129" class="Symbol">}}</a>
        <a id="9140" class="Comment">-------------------------------------</a>
      <a id="9184" class="Symbol">→</a> <a id="9186" href="simple_essence.html#9045" class="Bound">A</a> <a id="9188" class="Symbol">→</a> <a id="9190" href="simple_essence.html#7049" class="Record">LinMap</a> <a id="9197" href="simple_essence.html#9045" class="Bound">A</a> <a id="9199" href="simple_essence.html#6123" class="Datatype">§</a>
<a id="9201" href="simple_essence.html#9036" class="Function">a⊸§←a</a> <a id="9207" class="Symbol">=</a> <a id="9209" class="Symbol">λ</a> <a id="9211" class="Symbol">{</a> <a id="9213" href="simple_essence.html#9213" class="Bound">a</a> <a id="9215" class="Symbol">→</a> <a id="9217" href="simple_essence.html#7226" class="InductiveConstructor">mkLM</a> <a id="9222" class="Symbol">(</a><a id="9223" href="simple_essence.html#9213" class="Bound">a</a> <a id="9225" href="simple_essence.html#8040" class="Field Operator">·_</a><a id="9227" class="Symbol">)</a> <a id="9229" href="simple_essence.html#8118" class="Field">·-distrib-⊕</a> <a id="9241" href="simple_essence.html#8250" class="Field">·-comm-⊛</a> <a id="9250" class="Symbol">}</a>

<a id="9253" class="Comment">-- Danger, Will Robinson!</a>
<a id="9279" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9291" href="simple_essence.html#9291" class="Postulate">x·z≡y·z→x≡y</a> <a id="9303" class="Symbol">:</a> <a id="9305" class="Symbol">{</a><a id="9306" href="simple_essence.html#9306" class="Bound">A</a> <a id="9308" class="Symbol">:</a> <a id="9310" class="PrimitiveType">Set</a> <a id="9314" href="simple_essence.html#5509" class="Bound">a</a><a id="9315" class="Symbol">}</a>
                <a id="9333" class="Symbol">{{</a><a id="9335" href="simple_essence.html#9335" class="Bound">_</a> <a id="9337" class="Symbol">:</a> <a id="9339" href="simple_essence.html#6163" class="Record">Additive</a> <a id="9348" href="simple_essence.html#9306" class="Bound">A</a><a id="9349" class="Symbol">}}</a> <a id="9352" class="Symbol">{{</a><a id="9354" href="simple_essence.html#9354" class="Bound">_</a> <a id="9356" class="Symbol">:</a> <a id="9358" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="9367" href="simple_essence.html#9306" class="Bound">A</a><a id="9368" class="Symbol">}}</a> <a id="9371" class="Symbol">{{</a><a id="9373" href="simple_essence.html#9373" class="Bound">_</a> <a id="9375" class="Symbol">:</a> <a id="9377" href="simple_essence.html#7795" class="Record">VectorSpace</a> <a id="9389" href="simple_essence.html#9306" class="Bound">A</a><a id="9390" class="Symbol">}}</a>
                <a id="9409" class="Symbol">{</a><a id="9410" href="simple_essence.html#9410" class="Bound">x</a> <a id="9412" href="simple_essence.html#9412" class="Bound">y</a> <a id="9414" class="Symbol">:</a> <a id="9416" href="simple_essence.html#9306" class="Bound">A</a><a id="9417" class="Symbol">}</a>
              <a id="9433" class="Symbol">→</a> <a id="9435" class="Symbol">(∀</a> <a id="9438" class="Symbol">{</a><a id="9439" href="simple_essence.html#9439" class="Bound">z</a> <a id="9441" class="Symbol">:</a> <a id="9443" href="simple_essence.html#9306" class="Bound">A</a><a id="9444" class="Symbol">}</a> <a id="9446" class="Symbol">→</a> <a id="9448" href="simple_essence.html#9410" class="Bound">x</a> <a id="9450" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="9452" href="simple_essence.html#9439" class="Bound">z</a> <a id="9454" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9456" href="simple_essence.html#9412" class="Bound">y</a> <a id="9458" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="9460" href="simple_essence.html#9439" class="Bound">z</a><a id="9461" class="Symbol">)</a>
                <a id="9479" class="Comment">-----------------------------------------------------------</a>
              <a id="9553" class="Symbol">→</a> <a id="9555" href="simple_essence.html#9410" class="Bound">x</a> <a id="9557" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9559" href="simple_essence.html#9412" class="Bound">y</a>
<a id="9561" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9621" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9688" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9719" href="simple_essence.html#9719" class="Function">a⊸§↔a</a> <a id="9725" class="Symbol">:</a> <a id="9727" class="Symbol">{</a><a id="9728" href="simple_essence.html#9728" class="Bound">A</a> <a id="9730" class="Symbol">:</a> <a id="9732" class="PrimitiveType">Set</a> <a id="9736" href="simple_essence.html#5509" class="Bound">a</a><a id="9737" class="Symbol">}</a>
        <a id="9747" class="Symbol">{{</a><a id="9749" href="simple_essence.html#9749" class="Bound">_</a> <a id="9751" class="Symbol">:</a> <a id="9753" href="simple_essence.html#6163" class="Record">Additive</a> <a id="9762" href="simple_essence.html#9728" class="Bound">A</a><a id="9763" class="Symbol">}}</a> <a id="9766" class="Symbol">{{</a><a id="9768" href="simple_essence.html#9768" class="Bound">_</a> <a id="9770" class="Symbol">:</a> <a id="9772" href="simple_essence.html#6777" class="Record">Scalable</a> <a id="9781" href="simple_essence.html#9728" class="Bound">A</a><a id="9782" class="Symbol">}}</a>
        <a id="9793" class="Symbol">{{</a><a id="9795" href="simple_essence.html#9795" class="Bound">_</a> <a id="9797" class="Symbol">:</a> <a id="9799" href="simple_essence.html#7795" class="Record">VectorSpace</a> <a id="9811" href="simple_essence.html#9728" class="Bound">A</a><a id="9812" class="Symbol">}}</a>
        <a id="9823" class="Comment">-------------------------------------</a>
      <a id="9867" class="Symbol">→</a> <a id="9869" class="Symbol">(</a><a id="9870" href="simple_essence.html#7049" class="Record">LinMap</a> <a id="9877" href="simple_essence.html#9728" class="Bound">A</a> <a id="9879" href="simple_essence.html#6123" class="Datatype">§</a><a id="9880" class="Symbol">)</a> <a id="9882" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9884" href="simple_essence.html#9728" class="Bound">A</a>
<a id="9886" href="simple_essence.html#9719" class="Function">a⊸§↔a</a> <a id="9892" class="Symbol">{</a><a id="9893" href="simple_essence.html#9893" class="Bound">A</a><a id="9894" class="Symbol">}</a> <a id="9896" class="Symbol">=</a>
  <a id="9900" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9904" class="Symbol">{</a><a id="9905" class="Argument">f</a> <a id="9907" class="Symbol">=</a> <a id="9909" href="simple_essence.html#8794" class="Function">a⊸§→a</a><a id="9914" class="Symbol">}</a> <a id="9916" class="Symbol">{</a><a id="9917" class="Argument">f⁻¹</a> <a id="9921" class="Symbol">=</a> <a id="9923" href="simple_essence.html#9036" class="Function">a⊸§←a</a><a id="9928" class="Symbol">}</a>
      <a id="9936" class="Symbol">(</a> <a id="9938" class="Symbol">(λ</a> <a id="9941" class="Symbol">{</a><a id="9942" href="simple_essence.html#9942" class="Bound">x</a> <a id="9944" class="Symbol">→</a> <a id="9946" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="9970" href="simple_essence.html#8794" class="Function">a⊸§→a</a> <a id="9976" class="Symbol">(</a><a id="9977" href="simple_essence.html#9036" class="Function">a⊸§←a</a> <a id="9983" href="simple_essence.html#9942" class="Bound">x</a><a id="9984" class="Symbol">)</a>
                <a id="10002" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10024" href="simple_essence.html#8794" class="Function">a⊸§→a</a> <a id="10030" class="Symbol">(</a><a id="10031" href="simple_essence.html#7226" class="InductiveConstructor">mkLM</a> <a id="10036" class="Symbol">(</a><a id="10037" href="simple_essence.html#9942" class="Bound">x</a> <a id="10039" href="simple_essence.html#8040" class="Field Operator">·_</a><a id="10041" class="Symbol">)</a> <a id="10043" href="simple_essence.html#8118" class="Field">·-distrib-⊕</a> <a id="10055" href="simple_essence.html#8250" class="Field">·-comm-⊛</a><a id="10063" class="Symbol">)</a>
                <a id="10081" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10103" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10109" class="Symbol">(λ</a> <a id="10112" href="simple_essence.html#10112" class="Bound">acc</a> <a id="10116" href="simple_essence.html#10116" class="Bound">v</a> <a id="10118" class="Symbol">→</a> <a id="10120" href="simple_essence.html#10112" class="Bound">acc</a> <a id="10124" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="10126" class="Symbol">(</a><a id="10127" href="simple_essence.html#9942" class="Bound">x</a> <a id="10129" href="simple_essence.html#8040" class="Field Operator">·</a> <a id="10131" href="simple_essence.html#10116" class="Bound">v</a><a id="10132" class="Symbol">)</a> <a id="10134" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="10136" href="simple_essence.html#10116" class="Bound">v</a><a id="10137" class="Symbol">)</a> <a id="10139" href="simple_essence.html#6276" class="Field">id⊕</a> <a id="10143" href="simple_essence.html#8015" class="Field">basisSet</a>
                <a id="10168" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10171" href="simple_essence.html#9291" class="Postulate">x·z≡y·z→x≡y</a> <a id="10183" class="Symbol">(</a><a id="10184" href="simple_essence.html#8518" class="Field">orthonormal</a> <a id="10196" class="Symbol">{</a><a id="10197" class="Argument">f</a> <a id="10199" class="Symbol">=</a> <a id="10201" class="Symbol">(</a><a id="10202" href="simple_essence.html#9942" class="Bound">x</a> <a id="10204" href="simple_essence.html#8040" class="Field Operator">·_</a><a id="10206" class="Symbol">)})</a> <a id="10210" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10230" href="simple_essence.html#9942" class="Bound">x</a>
                <a id="10248" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10249" class="Symbol">})</a>
      <a id="10258" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10260" class="Symbol">λ</a> <a id="10262" class="Symbol">{</a><a id="10263" href="simple_essence.html#10263" class="Bound">lm</a> <a id="10266" class="Symbol">→</a> <a id="10268" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10292" href="simple_essence.html#9036" class="Function">a⊸§←a</a> <a id="10298" class="Symbol">(</a><a id="10299" href="simple_essence.html#8794" class="Function">a⊸§→a</a> <a id="10305" href="simple_essence.html#10263" class="Bound">lm</a><a id="10307" class="Symbol">)</a>
                <a id="10325" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10347" href="simple_essence.html#9036" class="Function">a⊸§←a</a> <a id="10353" class="Symbol">(</a><a id="10354" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10360" class="Symbol">(λ</a> <a id="10363" href="simple_essence.html#10363" class="Bound">acc</a> <a id="10367" href="simple_essence.html#10367" class="Bound">v</a> <a id="10369" class="Symbol">→</a> <a id="10371" href="simple_essence.html#10363" class="Bound">acc</a> <a id="10375" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="10377" class="Symbol">(</a><a id="10378" href="simple_essence.html#7243" class="Field">LinMap.f</a> <a id="10387" href="simple_essence.html#10263" class="Bound">lm</a> <a id="10390" href="simple_essence.html#10367" class="Bound">v</a><a id="10391" class="Symbol">)</a> <a id="10393" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="10395" href="simple_essence.html#10367" class="Bound">v</a><a id="10396" class="Symbol">)</a> <a id="10398" href="simple_essence.html#6276" class="Field">id⊕</a> <a id="10402" href="simple_essence.html#8015" class="Field">basisSet</a><a id="10410" class="Symbol">)</a>
                <a id="10428" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10450" href="simple_essence.html#7226" class="InductiveConstructor">mkLM</a> <a id="10455" class="Symbol">((</a><a id="10457" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10463" class="Symbol">(λ</a> <a id="10466" href="simple_essence.html#10466" class="Bound">acc</a> <a id="10470" href="simple_essence.html#10470" class="Bound">v</a> <a id="10472" class="Symbol">→</a> <a id="10474" href="simple_essence.html#10466" class="Bound">acc</a> <a id="10478" href="simple_essence.html#6289" class="Field Operator">⊕</a> <a id="10480" class="Symbol">(</a><a id="10481" href="simple_essence.html#7243" class="Field">LinMap.f</a> <a id="10490" href="simple_essence.html#10263" class="Bound">lm</a> <a id="10493" href="simple_essence.html#10470" class="Bound">v</a><a id="10494" class="Symbol">)</a> <a id="10496" href="simple_essence.html#6890" class="Field Operator">⊛</a> <a id="10498" href="simple_essence.html#10470" class="Bound">v</a><a id="10499" class="Symbol">)</a> <a id="10501" href="simple_essence.html#6276" class="Field">id⊕</a> <a id="10505" href="simple_essence.html#8015" class="Field">basisSet</a><a id="10513" class="Symbol">)</a><a id="10514" href="simple_essence.html#8040" class="Field Operator">·_</a><a id="10516" class="Symbol">)</a>
                       <a id="10541" href="simple_essence.html#8118" class="Field">·-distrib-⊕</a> <a id="10553" href="simple_essence.html#8250" class="Field">·-comm-⊛</a>
                <a id="10578" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10581" href="simple_essence.html#7561" class="Postulate">⊸≡</a> <a id="10584" class="Symbol">(</a> <a id="10586" href="simple_essence.html#6042" class="Postulate">extensionality</a>
                          <a id="10627" class="Symbol">(</a> <a id="10629" class="Symbol">λ</a> <a id="10631" href="simple_essence.html#10631" class="Bound">x</a> <a id="10633" class="Symbol">→</a> <a id="10635" href="simple_essence.html#8518" class="Field">orthonormal</a> <a id="10647" class="Symbol">{</a><a id="10648" class="Argument">f</a> <a id="10650" class="Symbol">=</a> <a id="10652" href="simple_essence.html#7243" class="Field">LinMap.f</a> <a id="10661" href="simple_essence.html#10263" class="Bound">lm</a><a id="10663" class="Symbol">}</a> <a id="10665" class="Symbol">{</a><a id="10666" class="Argument">x</a> <a id="10668" class="Symbol">=</a> <a id="10670" href="simple_essence.html#10631" class="Bound">x</a><a id="10671" class="Symbol">}</a> <a id="10673" class="Symbol">)</a>
                      <a id="10697" class="Symbol">)</a>
                 <a id="10716" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10736" href="simple_essence.html#10263" class="Bound">lm</a>
                <a id="10755" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10756" class="Symbol">}</a>
      <a id="10764" class="Symbol">)</a>

<a id="10767" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10850" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10912" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="11006" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="11069" class="Comment">--</a>
<a id="11072" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="11095" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="11144" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="11177" class="Comment">--         -------------------------------------</a>
<a id="11226" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11254" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>