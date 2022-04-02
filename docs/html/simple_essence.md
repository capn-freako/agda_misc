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

<pre class="Agda"><a id="5432" class="Keyword">module</a> <a id="5439" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5454" class="Symbol">{</a><a id="5455" href="simple_essence.html#5455" class="Bound">s</a> <a id="5457" href="simple_essence.html#5457" class="Bound">a</a> <a id="5459" href="simple_essence.html#5459" class="Bound">b</a><a id="5460" class="Symbol">}</a> <a id="5462" class="Keyword">where</a>

<a id="5469" class="Keyword">open</a> <a id="5474" class="Keyword">import</a> <a id="5481" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5500" class="Keyword">open</a> <a id="5505" class="Keyword">import</a> <a id="5512" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5547" class="Keyword">using</a> <a id="5553" class="Symbol">(</a><a id="5554" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5568" class="Symbol">)</a>
<a id="5570" class="Keyword">open</a> <a id="5575" class="Keyword">import</a> <a id="5582" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5593" class="Keyword">open</a> <a id="5598" class="Keyword">import</a> <a id="5605" href="Data.List.html" class="Module">Data.List</a>
<a id="5615" class="Keyword">open</a> <a id="5620" class="Keyword">import</a> <a id="5627" href="Function.html" class="Module">Function</a> <a id="5636" class="Keyword">using</a> <a id="5642" class="Symbol">(</a><a id="5643" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5646" class="Symbol">;</a> <a id="5648" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5651" class="Symbol">;</a> <a id="5653" href="Function.Base.html#615" class="Function">id</a><a id="5655" class="Symbol">)</a>
<a id="5657" class="Keyword">open</a> <a id="5662" class="Keyword">import</a> <a id="5669" href="Level.html" class="Module">Level</a> <a id="5675" class="Keyword">using</a> <a id="5681" class="Symbol">(</a><a id="5682" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5687" class="Symbol">;</a> <a id="5689" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5692" class="Symbol">)</a>

<a id="5695" class="Keyword">import</a> <a id="5702" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5740" class="Symbol">as</a> <a id="5743" class="Module">Eq</a>
<a id="5746" class="Keyword">open</a> <a id="5751" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5754" class="Keyword">using</a> <a id="5760" class="Symbol">(</a><a id="5761" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5764" class="Symbol">;</a> <a id="5766" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5770" class="Symbol">;</a> <a id="5772" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5777" class="Symbol">;</a> <a id="5779" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5782" class="Symbol">;</a> <a id="5784" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5788" class="Symbol">;</a> <a id="5790" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5795" class="Symbol">;</a> <a id="5797" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5805" class="Symbol">;</a> <a id="5807" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5812" class="Symbol">)</a>
<a id="5814" class="Keyword">open</a> <a id="5819" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5834" class="Keyword">using</a> <a id="5840" class="Symbol">(</a><a id="5841" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5847" class="Symbol">;</a> <a id="5849" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5854" class="Symbol">;</a> <a id="5856" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5862" class="Symbol">;</a> <a id="5864" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5866" class="Symbol">)</a>

<a id="5869" class="Keyword">postulate</a>
  <a id="5881" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="5956" href="simple_essence.html#5956" class="Postulate">id+</a> <a id="5960" class="Symbol">:</a> <a id="5962" class="Symbol">{</a><a id="5963" href="simple_essence.html#5963" class="Bound">x</a> <a id="5965" class="Symbol">:</a> <a id="5967" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="5972" class="Symbol">}</a> <a id="5974" class="Symbol">→</a> <a id="5976" class="Number">0.0</a> <a id="5980" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="5982" href="simple_essence.html#5963" class="Bound">x</a> <a id="5984" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5986" href="simple_essence.html#5963" class="Bound">x</a>
  <a id="extensionality"></a><a id="5990" href="simple_essence.html#5990" class="Postulate">extensionality</a> <a id="6005" class="Symbol">:</a> <a id="6007" class="Symbol">∀</a> <a id="6009" class="Symbol">{</a><a id="6010" href="simple_essence.html#6010" class="Bound">ℓ₁</a> <a id="6013" href="simple_essence.html#6013" class="Bound">ℓ₂</a><a id="6015" class="Symbol">}</a> <a id="6017" class="Symbol">→</a> <a id="6019" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="6034" href="simple_essence.html#6010" class="Bound">ℓ₁</a> <a id="6037" href="simple_essence.html#6013" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="6041" href="simple_essence.html#6041" class="Function">ℓ</a> <a id="6043" class="Symbol">:</a> <a id="6045" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="6051" href="simple_essence.html#6041" class="Function">ℓ</a> <a id="6053" class="Symbol">=</a> <a id="6055" href="simple_essence.html#5455" class="Bound">s</a> <a id="6057" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6059" href="simple_essence.html#5457" class="Bound">a</a> <a id="6061" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6063" href="simple_essence.html#5459" class="Bound">b</a>

<a id="6066" class="Keyword">data</a> <a id="§"></a><a id="6071" href="simple_essence.html#6071" class="Datatype">§</a> <a id="6073" class="Symbol">:</a> <a id="6075" class="PrimitiveType">Set</a> <a id="6079" href="simple_essence.html#5457" class="Bound">a</a> <a id="6081" class="Keyword">where</a>
  <a id="§.S"></a><a id="6089" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6091" class="Symbol">:</a> <a id="6093" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="6099" class="Symbol">→</a> <a id="6101" href="simple_essence.html#6071" class="Datatype">§</a>

<a id="6104" class="Keyword">record</a> <a id="Additive"></a><a id="6111" href="simple_essence.html#6111" class="Record">Additive</a> <a id="6120" class="Symbol">(</a><a id="6121" href="simple_essence.html#6121" class="Bound">A</a> <a id="6123" class="Symbol">:</a> <a id="6125" class="PrimitiveType">Set</a> <a id="6129" href="simple_essence.html#5457" class="Bound">a</a><a id="6130" class="Symbol">)</a> <a id="6132" class="Symbol">:</a> <a id="6134" class="PrimitiveType">Set</a> <a id="6138" href="simple_essence.html#6041" class="Function">ℓ</a> <a id="6140" class="Keyword">where</a>
  <a id="6148" class="Keyword">infixl</a> <a id="6155" class="Number">6</a> <a id="6157" href="simple_essence.html#6237" class="Field Operator">_⊕_</a>  <a id="6162" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6214" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6224" href="simple_essence.html#6224" class="Field">id⊕</a>  <a id="6229" class="Symbol">:</a> <a id="6231" href="simple_essence.html#6121" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6237" href="simple_essence.html#6237" class="Field Operator">_⊕_</a>  <a id="6242" class="Symbol">:</a> <a id="6244" href="simple_essence.html#6121" class="Bound">A</a> <a id="6246" class="Symbol">→</a> <a id="6248" href="simple_essence.html#6121" class="Bound">A</a> <a id="6250" class="Symbol">→</a> <a id="6252" href="simple_essence.html#6121" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6258" href="simple_essence.html#6258" class="Field">id-⊕</a> <a id="6263" class="Symbol">:</a> <a id="6265" class="Symbol">(</a><a id="6266" href="simple_essence.html#6266" class="Bound">a</a> <a id="6268" class="Symbol">:</a> <a id="6270" href="simple_essence.html#6121" class="Bound">A</a><a id="6271" class="Symbol">)</a>
           <a id="6284" class="Comment">-----------</a>
         <a id="6305" class="Symbol">→</a> <a id="6307" href="simple_essence.html#6224" class="Field">id⊕</a> <a id="6311" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="6313" href="simple_essence.html#6266" class="Bound">a</a> <a id="6315" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6317" href="simple_essence.html#6266" class="Bound">a</a>
    <a id="6323" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6376" class="Keyword">open</a> <a id="6381" href="simple_essence.html#6111" class="Module">Additive</a> <a id="6390" class="Symbol">{{</a> <a id="6393" class="Symbol">...</a> <a id="6397" class="Symbol">}}</a>
<a id="6400" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6411" href="simple_essence.html#6411" class="Function">AdditiveScalar</a> <a id="6426" class="Symbol">:</a> <a id="6428" href="simple_essence.html#6111" class="Record">Additive</a> <a id="6437" href="simple_essence.html#6071" class="Datatype">§</a>
  <a id="6441" href="simple_essence.html#6411" class="Function">AdditiveScalar</a> <a id="6456" class="Symbol">=</a> <a id="6458" class="Keyword">record</a>
    <a id="6469" class="Symbol">{</a> <a id="6471" href="simple_essence.html#6224" class="Field">id⊕</a>  <a id="6476" class="Symbol">=</a> <a id="6478" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6480" class="Number">0.0</a>
    <a id="6488" class="Symbol">;</a> <a id="6490" href="simple_essence.html#6237" class="Field Operator">_⊕_</a>  <a id="6495" class="Symbol">=</a> <a id="6497" class="Symbol">λ</a> <a id="6499" class="Symbol">{(</a><a id="6501" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6503" href="simple_essence.html#6503" class="Bound">x</a><a id="6504" class="Symbol">)</a> <a id="6506" class="Symbol">(</a><a id="6507" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6509" href="simple_essence.html#6509" class="Bound">y</a><a id="6510" class="Symbol">)</a> <a id="6512" class="Symbol">→</a> <a id="6514" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6516" class="Symbol">(</a><a id="6517" href="simple_essence.html#6503" class="Bound">x</a> <a id="6519" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6521" href="simple_essence.html#6509" class="Bound">y</a><a id="6522" class="Symbol">)}</a>
    <a id="6529" class="Symbol">;</a> <a id="6531" href="simple_essence.html#6258" class="Field">id-⊕</a> <a id="6536" class="Symbol">=</a> <a id="6538" class="Symbol">λ</a> <a id="6540" class="Symbol">{</a> <a id="6542" class="Symbol">(</a><a id="6543" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6545" href="simple_essence.html#6545" class="Bound">x</a><a id="6546" class="Symbol">)</a> <a id="6548" class="Symbol">→</a> <a id="6550" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6583" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6585" class="Symbol">(</a><a id="6586" class="Number">0.0</a> <a id="6590" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6592" href="simple_essence.html#6545" class="Bound">x</a><a id="6593" class="Symbol">)</a>
                         <a id="6620" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6623" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6628" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6630" href="simple_essence.html#5956" class="Postulate">id+</a> <a id="6634" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6663" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6665" href="simple_essence.html#6545" class="Bound">x</a>
                         <a id="6692" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6709" class="Symbol">}</a>
    <a id="6715" class="Symbol">}</a>

<a id="6718" class="Keyword">record</a> <a id="Scalable"></a><a id="6725" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="6734" class="Symbol">(</a><a id="6735" href="simple_essence.html#6735" class="Bound">A</a> <a id="6737" class="Symbol">:</a> <a id="6739" class="PrimitiveType">Set</a> <a id="6743" href="simple_essence.html#5457" class="Bound">a</a><a id="6744" class="Symbol">)</a> <a id="6746" class="Symbol">:</a> <a id="6748" class="PrimitiveType">Set</a> <a id="6752" href="simple_essence.html#6041" class="Function">ℓ</a> <a id="6754" class="Keyword">where</a>
  <a id="6762" class="Keyword">infixl</a> <a id="6769" class="Number">7</a> <a id="6771" href="simple_essence.html#6838" class="Field Operator">_⊛_</a>  <a id="6776" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6828" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6838" href="simple_essence.html#6838" class="Field Operator">_⊛_</a> <a id="6842" class="Symbol">:</a> <a id="6844" href="simple_essence.html#6071" class="Datatype">§</a> <a id="6846" class="Symbol">→</a> <a id="6848" href="simple_essence.html#6735" class="Bound">A</a> <a id="6850" class="Symbol">→</a> <a id="6852" href="simple_essence.html#6735" class="Bound">A</a>
<a id="6854" class="Keyword">open</a> <a id="6859" href="simple_essence.html#6725" class="Module">Scalable</a> <a id="6868" class="Symbol">{{</a> <a id="6871" class="Symbol">...</a> <a id="6875" class="Symbol">}}</a>
<a id="6878" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="6889" href="simple_essence.html#6889" class="Function">ScalableScalar</a> <a id="6904" class="Symbol">:</a> <a id="6906" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="6915" href="simple_essence.html#6071" class="Datatype">§</a>
  <a id="6919" href="simple_essence.html#6889" class="Function">ScalableScalar</a> <a id="6934" class="Symbol">=</a> <a id="6936" class="Keyword">record</a>
    <a id="6947" class="Symbol">{</a> <a id="6949" href="simple_essence.html#6838" class="Field Operator">_⊛_</a> <a id="6953" class="Symbol">=</a> <a id="6955" class="Symbol">λ</a> <a id="6957" class="Symbol">{(</a><a id="6959" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6961" href="simple_essence.html#6961" class="Bound">x</a><a id="6962" class="Symbol">)</a> <a id="6964" class="Symbol">(</a><a id="6965" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6967" href="simple_essence.html#6967" class="Bound">y</a><a id="6968" class="Symbol">)</a> <a id="6970" class="Symbol">→</a> <a id="6972" href="simple_essence.html#6089" class="InductiveConstructor">S</a> <a id="6974" class="Symbol">(</a><a id="6975" href="simple_essence.html#6961" class="Bound">x</a> <a id="6977" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="6979" href="simple_essence.html#6967" class="Bound">y</a><a id="6980" class="Symbol">)}</a>
    <a id="6987" class="Symbol">}</a>

<a id="6990" class="Keyword">record</a> <a id="LinMap"></a><a id="6997" href="simple_essence.html#6997" class="Record">LinMap</a> <a id="7004" class="Symbol">(</a><a id="7005" href="simple_essence.html#7005" class="Bound">A</a> <a id="7007" class="Symbol">:</a> <a id="7009" class="PrimitiveType">Set</a> <a id="7013" href="simple_essence.html#5457" class="Bound">a</a><a id="7014" class="Symbol">)</a> <a id="7016" class="Symbol">(</a><a id="7017" href="simple_essence.html#7017" class="Bound">B</a> <a id="7019" class="Symbol">:</a> <a id="7021" class="PrimitiveType">Set</a> <a id="7025" href="simple_essence.html#5457" class="Bound">a</a><a id="7026" class="Symbol">)</a>
              <a id="7042" class="Symbol">{{</a><a id="7044" href="simple_essence.html#7044" class="Bound">_</a> <a id="7046" class="Symbol">:</a> <a id="7048" href="simple_essence.html#6111" class="Record">Additive</a> <a id="7057" href="simple_essence.html#7005" class="Bound">A</a><a id="7058" class="Symbol">}}</a> <a id="7061" class="Symbol">{{</a><a id="7063" href="simple_essence.html#7063" class="Bound">_</a> <a id="7065" class="Symbol">:</a> <a id="7067" href="simple_essence.html#6111" class="Record">Additive</a> <a id="7076" href="simple_essence.html#7017" class="Bound">B</a><a id="7077" class="Symbol">}}</a>
              <a id="7094" class="Symbol">{{</a><a id="7096" href="simple_essence.html#7096" class="Bound">_</a> <a id="7098" class="Symbol">:</a> <a id="7100" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="7109" href="simple_essence.html#7005" class="Bound">A</a><a id="7110" class="Symbol">}}</a> <a id="7113" class="Symbol">{{</a><a id="7115" href="simple_essence.html#7115" class="Bound">_</a> <a id="7117" class="Symbol">:</a> <a id="7119" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="7128" href="simple_essence.html#7017" class="Bound">B</a><a id="7129" class="Symbol">}}</a>
              <a id="7146" class="Symbol">:</a> <a id="7148" class="PrimitiveType">Set</a> <a id="7152" href="simple_essence.html#6041" class="Function">ℓ</a> <a id="7154" class="Keyword">where</a>
  <a id="7162" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7174" href="simple_essence.html#7174" class="InductiveConstructor">mkLM</a>
  <a id="7181" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7191" href="simple_essence.html#7191" class="Field">f</a>      <a id="7198" class="Symbol">:</a> <a id="7200" href="simple_essence.html#7005" class="Bound">A</a> <a id="7202" class="Symbol">→</a> <a id="7204" href="simple_essence.html#7017" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7211" href="simple_essence.html#7211" class="Field">adds</a>   <a id="7218" class="Symbol">:</a> <a id="7220" class="Symbol">∀</a> <a id="7222" class="Symbol">{</a><a id="7223" href="simple_essence.html#7223" class="Bound">a</a> <a id="7225" href="simple_essence.html#7225" class="Bound">b</a> <a id="7227" class="Symbol">:</a> <a id="7229" href="simple_essence.html#7005" class="Bound">A</a><a id="7230" class="Symbol">}</a>
             <a id="7245" class="Comment">---------------------</a>
           <a id="7278" class="Symbol">→</a> <a id="7280" href="simple_essence.html#7191" class="Field">f</a> <a id="7282" class="Symbol">(</a><a id="7283" href="simple_essence.html#7223" class="Bound">a</a> <a id="7285" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="7287" href="simple_essence.html#7225" class="Bound">b</a><a id="7288" class="Symbol">)</a> <a id="7290" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7292" href="simple_essence.html#7191" class="Field">f</a> <a id="7294" href="simple_essence.html#7223" class="Bound">a</a> <a id="7296" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="7298" href="simple_essence.html#7191" class="Field">f</a> <a id="7300" href="simple_essence.html#7225" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7307" href="simple_essence.html#7307" class="Field">scales</a> <a id="7314" class="Symbol">:</a> <a id="7316" class="Symbol">∀</a> <a id="7318" class="Symbol">{</a><a id="7319" href="simple_essence.html#7319" class="Bound">s</a> <a id="7321" class="Symbol">:</a> <a id="7323" href="simple_essence.html#6071" class="Datatype">§</a><a id="7324" class="Symbol">}</a> <a id="7326" class="Symbol">{</a><a id="7327" href="simple_essence.html#7327" class="Bound">a</a> <a id="7329" class="Symbol">:</a> <a id="7331" href="simple_essence.html#7005" class="Bound">A</a><a id="7332" class="Symbol">}</a>
             <a id="7347" class="Comment">-------------------</a>
           <a id="7378" class="Symbol">→</a> <a id="7380" href="simple_essence.html#7191" class="Field">f</a> <a id="7382" class="Symbol">(</a><a id="7383" href="simple_essence.html#7319" class="Bound">s</a> <a id="7385" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="7387" href="simple_essence.html#7327" class="Bound">a</a><a id="7388" class="Symbol">)</a> <a id="7390" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7392" href="simple_essence.html#7319" class="Bound">s</a> <a id="7394" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="7396" href="simple_essence.html#7191" class="Field">f</a> <a id="7398" href="simple_essence.html#7327" class="Bound">a</a>
<a id="7400" class="Keyword">open</a> <a id="7405" href="simple_essence.html#6997" class="Module">LinMap</a> <a id="7412" class="Symbol">{{</a> <a id="7415" class="Symbol">...</a> <a id="7419" class="Symbol">}}</a>

<a id="7423" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7449" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7497" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7509" href="simple_essence.html#7509" class="Postulate">⊸≡</a> <a id="7512" class="Symbol">:</a> <a id="7514" class="Symbol">{</a><a id="7515" href="simple_essence.html#7515" class="Bound">A</a> <a id="7517" href="simple_essence.html#7517" class="Bound">B</a> <a id="7519" class="Symbol">:</a> <a id="7521" class="PrimitiveType">Set</a> <a id="7525" href="simple_essence.html#5457" class="Bound">a</a><a id="7526" class="Symbol">}</a>
       <a id="7535" class="Symbol">{{</a><a id="7537" href="simple_essence.html#7537" class="Bound">_</a> <a id="7539" class="Symbol">:</a> <a id="7541" href="simple_essence.html#6111" class="Record">Additive</a> <a id="7550" href="simple_essence.html#7515" class="Bound">A</a><a id="7551" class="Symbol">}}</a> <a id="7554" class="Symbol">{{</a><a id="7556" href="simple_essence.html#7556" class="Bound">_</a> <a id="7558" class="Symbol">:</a> <a id="7560" href="simple_essence.html#6111" class="Record">Additive</a> <a id="7569" href="simple_essence.html#7517" class="Bound">B</a><a id="7570" class="Symbol">}}</a>
       <a id="7580" class="Symbol">{{</a><a id="7582" href="simple_essence.html#7582" class="Bound">_</a> <a id="7584" class="Symbol">:</a> <a id="7586" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="7595" href="simple_essence.html#7515" class="Bound">A</a><a id="7596" class="Symbol">}}</a> <a id="7599" class="Symbol">{{</a><a id="7601" href="simple_essence.html#7601" class="Bound">_</a> <a id="7603" class="Symbol">:</a> <a id="7605" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="7614" href="simple_essence.html#7517" class="Bound">B</a><a id="7615" class="Symbol">}}</a>
       <a id="7625" class="Symbol">{</a><a id="7626" href="simple_essence.html#7626" class="Bound">lm₁</a> <a id="7630" href="simple_essence.html#7630" class="Bound">lm₂</a> <a id="7634" class="Symbol">:</a> <a id="7636" href="simple_essence.html#6997" class="Record">LinMap</a> <a id="7643" href="simple_essence.html#7515" class="Bound">A</a> <a id="7645" href="simple_essence.html#7517" class="Bound">B</a><a id="7646" class="Symbol">}</a>
     <a id="7653" class="Symbol">→</a> <a id="7655" href="simple_essence.html#7191" class="Field">LinMap.f</a> <a id="7664" href="simple_essence.html#7626" class="Bound">lm₁</a> <a id="7668" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7670" href="simple_essence.html#7191" class="Field">LinMap.f</a> <a id="7679" href="simple_essence.html#7630" class="Bound">lm₂</a>
       <a id="7690" class="Comment">---------------------------</a>
     <a id="7723" class="Symbol">→</a> <a id="7725" href="simple_essence.html#7626" class="Bound">lm₁</a> <a id="7729" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7731" href="simple_essence.html#7630" class="Bound">lm₂</a>

<a id="7736" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7743" href="simple_essence.html#7743" class="Record">VectorSpace</a> <a id="7755" class="Symbol">(</a><a id="7756" href="simple_essence.html#7756" class="Bound">A</a> <a id="7758" class="Symbol">:</a> <a id="7760" class="PrimitiveType">Set</a> <a id="7764" href="simple_essence.html#5457" class="Bound">a</a><a id="7765" class="Symbol">)</a>
                   <a id="7786" class="Symbol">{{</a><a id="7788" href="simple_essence.html#7788" class="Bound">_</a> <a id="7790" class="Symbol">:</a> <a id="7792" href="simple_essence.html#6111" class="Record">Additive</a> <a id="7801" href="simple_essence.html#7756" class="Bound">A</a><a id="7802" class="Symbol">}}</a> <a id="7805" class="Symbol">{{</a><a id="7807" href="simple_essence.html#7807" class="Bound">_</a> <a id="7809" class="Symbol">:</a> <a id="7811" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="7820" href="simple_essence.html#7756" class="Bound">A</a><a id="7821" class="Symbol">}}</a>
                   <a id="7843" class="Symbol">:</a> <a id="7845" class="PrimitiveType">Set</a> <a id="7849" href="simple_essence.html#6041" class="Function">ℓ</a> <a id="7851" class="Keyword">where</a>
  <a id="7859" class="Keyword">field</a>
    <a id="7869" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="7963" href="simple_essence.html#7963" class="Field">basisSet</a>    <a id="7975" class="Symbol">:</a> <a id="7977" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="7982" href="simple_essence.html#7756" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="7988" href="simple_essence.html#7988" class="Field Operator">_·_</a>         <a id="8000" class="Symbol">:</a> <a id="8002" href="simple_essence.html#7756" class="Bound">A</a> <a id="8004" class="Symbol">→</a> <a id="8006" href="simple_essence.html#7756" class="Bound">A</a> <a id="8008" class="Symbol">→</a> <a id="8010" href="simple_essence.html#6071" class="Datatype">§</a>
    <a id="8016" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="8066" href="simple_essence.html#8066" class="Field">·-distrib-⊕</a> <a id="8078" class="Symbol">:</a> <a id="8080" class="Symbol">∀</a> <a id="8082" class="Symbol">{</a><a id="8083" href="simple_essence.html#8083" class="Bound">a</a> <a id="8085" href="simple_essence.html#8085" class="Bound">b</a> <a id="8087" href="simple_essence.html#8087" class="Bound">c</a> <a id="8089" class="Symbol">:</a> <a id="8091" href="simple_essence.html#7756" class="Bound">A</a><a id="8092" class="Symbol">}</a>
                  <a id="8112" class="Comment">-------------------------------</a>
                <a id="8160" class="Symbol">→</a> <a id="8162" href="simple_essence.html#8083" class="Bound">a</a> <a id="8164" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="8166" class="Symbol">(</a><a id="8167" href="simple_essence.html#8085" class="Bound">b</a> <a id="8169" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="8171" href="simple_essence.html#8087" class="Bound">c</a><a id="8172" class="Symbol">)</a> <a id="8174" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8176" class="Symbol">(</a><a id="8177" href="simple_essence.html#8083" class="Bound">a</a> <a id="8179" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="8181" href="simple_essence.html#8085" class="Bound">b</a><a id="8182" class="Symbol">)</a> <a id="8184" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="8186" class="Symbol">(</a><a id="8187" href="simple_essence.html#8083" class="Bound">a</a> <a id="8189" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="8191" href="simple_essence.html#8087" class="Bound">c</a><a id="8192" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8198" href="simple_essence.html#8198" class="Field">·-comm-⊛</a>    <a id="8210" class="Symbol">:</a> <a id="8212" class="Symbol">∀</a> <a id="8214" class="Symbol">{</a><a id="8215" href="simple_essence.html#8215" class="Bound">s</a> <a id="8217" class="Symbol">:</a> <a id="8219" href="simple_essence.html#6071" class="Datatype">§</a><a id="8220" class="Symbol">}</a> <a id="8222" class="Symbol">{</a><a id="8223" href="simple_essence.html#8223" class="Bound">a</a> <a id="8225" href="simple_essence.html#8225" class="Bound">b</a> <a id="8227" class="Symbol">:</a> <a id="8229" href="simple_essence.html#7756" class="Bound">A</a><a id="8230" class="Symbol">}</a>
                  <a id="8250" class="Comment">-------------------------</a>
                <a id="8292" class="Symbol">→</a> <a id="8294" href="simple_essence.html#8223" class="Bound">a</a> <a id="8296" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="8298" class="Symbol">(</a><a id="8299" href="simple_essence.html#8215" class="Bound">s</a> <a id="8301" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="8303" href="simple_essence.html#8225" class="Bound">b</a><a id="8304" class="Symbol">)</a> <a id="8306" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8308" href="simple_essence.html#8215" class="Bound">s</a> <a id="8310" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="8312" class="Symbol">(</a><a id="8313" href="simple_essence.html#8223" class="Bound">a</a> <a id="8315" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="8317" href="simple_essence.html#8225" class="Bound">b</a><a id="8318" class="Symbol">)</a>
    <a id="8324" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8408" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8466" href="simple_essence.html#8466" class="Field">orthonormal</a> <a id="8478" class="Symbol">:</a> <a id="8480" class="Symbol">∀</a> <a id="8482" class="Symbol">{</a><a id="8483" href="simple_essence.html#8483" class="Bound">f</a> <a id="8485" class="Symbol">:</a> <a id="8487" href="simple_essence.html#7756" class="Bound">A</a> <a id="8489" class="Symbol">→</a> <a id="8491" href="simple_essence.html#6071" class="Datatype">§</a><a id="8492" class="Symbol">}</a>
                <a id="8510" class="Symbol">→</a> <a id="8512" class="Symbol">{</a><a id="8513" href="simple_essence.html#8513" class="Bound">x</a> <a id="8515" class="Symbol">:</a> <a id="8517" href="simple_essence.html#7756" class="Bound">A</a><a id="8518" class="Symbol">}</a>
                  <a id="8538" class="Comment">----------------------------------------------------------</a>
                <a id="8613" class="Symbol">→</a> <a id="8615" class="Symbol">(</a><a id="8616" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8622" class="Symbol">(λ</a> <a id="8625" href="simple_essence.html#8625" class="Bound">acc</a> <a id="8629" href="simple_essence.html#8629" class="Bound">v</a> <a id="8631" class="Symbol">→</a> <a id="8633" href="simple_essence.html#8625" class="Bound">acc</a> <a id="8637" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="8639" class="Symbol">(</a><a id="8640" href="simple_essence.html#8483" class="Bound">f</a> <a id="8642" href="simple_essence.html#8629" class="Bound">v</a><a id="8643" class="Symbol">)</a> <a id="8645" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="8647" href="simple_essence.html#8629" class="Bound">v</a><a id="8648" class="Symbol">)</a> <a id="8650" href="simple_essence.html#6224" class="Field">id⊕</a> <a id="8654" href="simple_essence.html#7963" class="Field">basisSet</a><a id="8662" class="Symbol">)</a> <a id="8664" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="8666" href="simple_essence.html#8513" class="Bound">x</a> <a id="8668" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8670" href="simple_essence.html#8483" class="Bound">f</a> <a id="8672" href="simple_essence.html#8513" class="Bound">x</a>
<a id="8674" class="Keyword">open</a> <a id="8679" href="simple_essence.html#7743" class="Module">VectorSpace</a> <a id="8691" class="Symbol">{{</a> <a id="8694" class="Symbol">...</a> <a id="8698" class="Symbol">}}</a>

<a id="8702" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8742" href="simple_essence.html#8742" class="Function">a⊸§→a</a> <a id="8748" class="Symbol">:</a> <a id="8750" class="Symbol">{</a><a id="8751" href="simple_essence.html#8751" class="Bound">A</a> <a id="8753" class="Symbol">:</a> <a id="8755" class="PrimitiveType">Set</a> <a id="8759" href="simple_essence.html#5457" class="Bound">a</a><a id="8760" class="Symbol">}</a>
        <a id="8770" class="Symbol">{{</a><a id="8772" href="simple_essence.html#8772" class="Bound">_</a> <a id="8774" class="Symbol">:</a> <a id="8776" href="simple_essence.html#6111" class="Record">Additive</a> <a id="8785" href="simple_essence.html#8751" class="Bound">A</a><a id="8786" class="Symbol">}}</a> <a id="8789" class="Symbol">{{</a><a id="8791" href="simple_essence.html#8791" class="Bound">_</a> <a id="8793" class="Symbol">:</a> <a id="8795" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="8804" href="simple_essence.html#8751" class="Bound">A</a><a id="8805" class="Symbol">}}</a>
        <a id="8816" class="Symbol">{{</a><a id="8818" href="simple_essence.html#8818" class="Bound">_</a> <a id="8820" class="Symbol">:</a> <a id="8822" href="simple_essence.html#7743" class="Record">VectorSpace</a> <a id="8834" href="simple_essence.html#8751" class="Bound">A</a><a id="8835" class="Symbol">}}</a>
        <a id="8846" class="Comment">-------------------------------------</a>
      <a id="8890" class="Symbol">→</a> <a id="8892" href="simple_essence.html#6997" class="Record">LinMap</a> <a id="8899" href="simple_essence.html#8751" class="Bound">A</a> <a id="8901" href="simple_essence.html#6071" class="Datatype">§</a> <a id="8903" class="Symbol">→</a> <a id="8905" href="simple_essence.html#8751" class="Bound">A</a>
<a id="8907" href="simple_essence.html#8742" class="Function">a⊸§→a</a> <a id="8913" class="Symbol">=</a> <a id="8915" class="Symbol">λ</a> <a id="8917" class="Symbol">{</a> <a id="8919" href="simple_essence.html#8919" class="Bound">lm</a> <a id="8922" class="Symbol">→</a> <a id="8924" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8930" class="Symbol">(λ</a> <a id="8933" href="simple_essence.html#8933" class="Bound">acc</a> <a id="8937" href="simple_essence.html#8937" class="Bound">v</a> <a id="8939" class="Symbol">→</a> <a id="8941" href="simple_essence.html#8933" class="Bound">acc</a> <a id="8945" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="8947" class="Symbol">(</a><a id="8948" href="simple_essence.html#7191" class="Field">LinMap.f</a> <a id="8957" href="simple_essence.html#8919" class="Bound">lm</a> <a id="8960" href="simple_essence.html#8937" class="Bound">v</a><a id="8961" class="Symbol">)</a> <a id="8963" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="8965" href="simple_essence.html#8937" class="Bound">v</a><a id="8966" class="Symbol">)</a> <a id="8968" href="simple_essence.html#6224" class="Field">id⊕</a> <a id="8972" href="simple_essence.html#7963" class="Field">basisSet</a> <a id="8981" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="8984" href="simple_essence.html#8984" class="Function">a⊸§←a</a> <a id="8990" class="Symbol">:</a> <a id="8992" class="Symbol">{</a><a id="8993" href="simple_essence.html#8993" class="Bound">A</a> <a id="8995" class="Symbol">:</a> <a id="8997" class="PrimitiveType">Set</a> <a id="9001" href="simple_essence.html#5457" class="Bound">a</a><a id="9002" class="Symbol">}</a>
        <a id="9012" class="Symbol">{{</a><a id="9014" href="simple_essence.html#9014" class="Bound">_</a> <a id="9016" class="Symbol">:</a> <a id="9018" href="simple_essence.html#6111" class="Record">Additive</a> <a id="9027" href="simple_essence.html#8993" class="Bound">A</a><a id="9028" class="Symbol">}}</a> <a id="9031" class="Symbol">{{</a><a id="9033" href="simple_essence.html#9033" class="Bound">_</a> <a id="9035" class="Symbol">:</a> <a id="9037" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="9046" href="simple_essence.html#8993" class="Bound">A</a><a id="9047" class="Symbol">}}</a>
        <a id="9058" class="Symbol">{{</a><a id="9060" href="simple_essence.html#9060" class="Bound">_</a> <a id="9062" class="Symbol">:</a> <a id="9064" href="simple_essence.html#7743" class="Record">VectorSpace</a> <a id="9076" href="simple_essence.html#8993" class="Bound">A</a><a id="9077" class="Symbol">}}</a>
        <a id="9088" class="Comment">-------------------------------------</a>
      <a id="9132" class="Symbol">→</a> <a id="9134" href="simple_essence.html#8993" class="Bound">A</a> <a id="9136" class="Symbol">→</a> <a id="9138" href="simple_essence.html#6997" class="Record">LinMap</a> <a id="9145" href="simple_essence.html#8993" class="Bound">A</a> <a id="9147" href="simple_essence.html#6071" class="Datatype">§</a>
<a id="9149" href="simple_essence.html#8984" class="Function">a⊸§←a</a> <a id="9155" class="Symbol">=</a> <a id="9157" class="Symbol">λ</a> <a id="9159" class="Symbol">{</a> <a id="9161" href="simple_essence.html#9161" class="Bound">a</a> <a id="9163" class="Symbol">→</a> <a id="9165" href="simple_essence.html#7174" class="InductiveConstructor">mkLM</a> <a id="9170" class="Symbol">(</a><a id="9171" href="simple_essence.html#9161" class="Bound">a</a> <a id="9173" href="simple_essence.html#7988" class="Field Operator">·_</a><a id="9175" class="Symbol">)</a> <a id="9177" href="simple_essence.html#8066" class="Field">·-distrib-⊕</a> <a id="9189" href="simple_essence.html#8198" class="Field">·-comm-⊛</a> <a id="9198" class="Symbol">}</a>

<a id="9201" class="Comment">-- Danger, Will Robinson!</a>
<a id="9227" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9239" href="simple_essence.html#9239" class="Postulate">x·z≡y·z→x≡y</a> <a id="9251" class="Symbol">:</a> <a id="9253" class="Symbol">{</a><a id="9254" href="simple_essence.html#9254" class="Bound">A</a> <a id="9256" class="Symbol">:</a> <a id="9258" class="PrimitiveType">Set</a> <a id="9262" href="simple_essence.html#5457" class="Bound">a</a><a id="9263" class="Symbol">}</a>
                <a id="9281" class="Symbol">{{</a><a id="9283" href="simple_essence.html#9283" class="Bound">_</a> <a id="9285" class="Symbol">:</a> <a id="9287" href="simple_essence.html#6111" class="Record">Additive</a> <a id="9296" href="simple_essence.html#9254" class="Bound">A</a><a id="9297" class="Symbol">}}</a> <a id="9300" class="Symbol">{{</a><a id="9302" href="simple_essence.html#9302" class="Bound">_</a> <a id="9304" class="Symbol">:</a> <a id="9306" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="9315" href="simple_essence.html#9254" class="Bound">A</a><a id="9316" class="Symbol">}}</a> <a id="9319" class="Symbol">{{</a><a id="9321" href="simple_essence.html#9321" class="Bound">_</a> <a id="9323" class="Symbol">:</a> <a id="9325" href="simple_essence.html#7743" class="Record">VectorSpace</a> <a id="9337" href="simple_essence.html#9254" class="Bound">A</a><a id="9338" class="Symbol">}}</a>
                <a id="9357" class="Symbol">{</a><a id="9358" href="simple_essence.html#9358" class="Bound">x</a> <a id="9360" href="simple_essence.html#9360" class="Bound">y</a> <a id="9362" class="Symbol">:</a> <a id="9364" href="simple_essence.html#9254" class="Bound">A</a><a id="9365" class="Symbol">}</a>
              <a id="9381" class="Symbol">→</a> <a id="9383" class="Symbol">(∀</a> <a id="9386" class="Symbol">{</a><a id="9387" href="simple_essence.html#9387" class="Bound">z</a> <a id="9389" class="Symbol">:</a> <a id="9391" href="simple_essence.html#9254" class="Bound">A</a><a id="9392" class="Symbol">}</a> <a id="9394" class="Symbol">→</a> <a id="9396" href="simple_essence.html#9358" class="Bound">x</a> <a id="9398" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="9400" href="simple_essence.html#9387" class="Bound">z</a> <a id="9402" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9404" href="simple_essence.html#9360" class="Bound">y</a> <a id="9406" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="9408" href="simple_essence.html#9387" class="Bound">z</a><a id="9409" class="Symbol">)</a>
                <a id="9427" class="Comment">-----------------------------------------------------------</a>
              <a id="9501" class="Symbol">→</a> <a id="9503" href="simple_essence.html#9358" class="Bound">x</a> <a id="9505" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9507" href="simple_essence.html#9360" class="Bound">y</a>
<a id="9509" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9569" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9636" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9667" href="simple_essence.html#9667" class="Function">a⊸§↔a</a> <a id="9673" class="Symbol">:</a> <a id="9675" class="Symbol">{</a><a id="9676" href="simple_essence.html#9676" class="Bound">A</a> <a id="9678" class="Symbol">:</a> <a id="9680" class="PrimitiveType">Set</a> <a id="9684" href="simple_essence.html#5457" class="Bound">a</a><a id="9685" class="Symbol">}</a>
        <a id="9695" class="Symbol">{{</a><a id="9697" href="simple_essence.html#9697" class="Bound">_</a> <a id="9699" class="Symbol">:</a> <a id="9701" href="simple_essence.html#6111" class="Record">Additive</a> <a id="9710" href="simple_essence.html#9676" class="Bound">A</a><a id="9711" class="Symbol">}}</a> <a id="9714" class="Symbol">{{</a><a id="9716" href="simple_essence.html#9716" class="Bound">_</a> <a id="9718" class="Symbol">:</a> <a id="9720" href="simple_essence.html#6725" class="Record">Scalable</a> <a id="9729" href="simple_essence.html#9676" class="Bound">A</a><a id="9730" class="Symbol">}}</a>
        <a id="9741" class="Symbol">{{</a><a id="9743" href="simple_essence.html#9743" class="Bound">_</a> <a id="9745" class="Symbol">:</a> <a id="9747" href="simple_essence.html#7743" class="Record">VectorSpace</a> <a id="9759" href="simple_essence.html#9676" class="Bound">A</a><a id="9760" class="Symbol">}}</a>
        <a id="9771" class="Comment">-------------------------------------</a>
      <a id="9815" class="Symbol">→</a> <a id="9817" class="Symbol">(</a><a id="9818" href="simple_essence.html#6997" class="Record">LinMap</a> <a id="9825" href="simple_essence.html#9676" class="Bound">A</a> <a id="9827" href="simple_essence.html#6071" class="Datatype">§</a><a id="9828" class="Symbol">)</a> <a id="9830" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9832" href="simple_essence.html#9676" class="Bound">A</a>
<a id="9834" href="simple_essence.html#9667" class="Function">a⊸§↔a</a> <a id="9840" class="Symbol">{</a><a id="9841" href="simple_essence.html#9841" class="Bound">A</a><a id="9842" class="Symbol">}</a> <a id="9844" class="Symbol">=</a>
  <a id="9848" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9852" class="Symbol">{</a><a id="9853" class="Argument">f</a> <a id="9855" class="Symbol">=</a> <a id="9857" href="simple_essence.html#8742" class="Function">a⊸§→a</a><a id="9862" class="Symbol">}</a> <a id="9864" class="Symbol">{</a><a id="9865" class="Argument">f⁻¹</a> <a id="9869" class="Symbol">=</a> <a id="9871" href="simple_essence.html#8984" class="Function">a⊸§←a</a><a id="9876" class="Symbol">}</a>
      <a id="9884" class="Symbol">(</a> <a id="9886" class="Symbol">(λ</a> <a id="9889" class="Symbol">{</a><a id="9890" href="simple_essence.html#9890" class="Bound">x</a> <a id="9892" class="Symbol">→</a> <a id="9894" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="9918" href="simple_essence.html#8742" class="Function">a⊸§→a</a> <a id="9924" class="Symbol">(</a><a id="9925" href="simple_essence.html#8984" class="Function">a⊸§←a</a> <a id="9931" href="simple_essence.html#9890" class="Bound">x</a><a id="9932" class="Symbol">)</a>
                <a id="9950" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9972" href="simple_essence.html#8742" class="Function">a⊸§→a</a> <a id="9978" class="Symbol">(</a><a id="9979" href="simple_essence.html#7174" class="InductiveConstructor">mkLM</a> <a id="9984" class="Symbol">(</a><a id="9985" href="simple_essence.html#9890" class="Bound">x</a> <a id="9987" href="simple_essence.html#7988" class="Field Operator">·_</a><a id="9989" class="Symbol">)</a> <a id="9991" href="simple_essence.html#8066" class="Field">·-distrib-⊕</a> <a id="10003" href="simple_essence.html#8198" class="Field">·-comm-⊛</a><a id="10011" class="Symbol">)</a>
                <a id="10029" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10051" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10057" class="Symbol">(λ</a> <a id="10060" href="simple_essence.html#10060" class="Bound">acc</a> <a id="10064" href="simple_essence.html#10064" class="Bound">v</a> <a id="10066" class="Symbol">→</a> <a id="10068" href="simple_essence.html#10060" class="Bound">acc</a> <a id="10072" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="10074" class="Symbol">(</a><a id="10075" href="simple_essence.html#9890" class="Bound">x</a> <a id="10077" href="simple_essence.html#7988" class="Field Operator">·</a> <a id="10079" href="simple_essence.html#10064" class="Bound">v</a><a id="10080" class="Symbol">)</a> <a id="10082" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="10084" href="simple_essence.html#10064" class="Bound">v</a><a id="10085" class="Symbol">)</a> <a id="10087" href="simple_essence.html#6224" class="Field">id⊕</a> <a id="10091" href="simple_essence.html#7963" class="Field">basisSet</a>
                <a id="10116" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10119" href="simple_essence.html#9239" class="Postulate">x·z≡y·z→x≡y</a> <a id="10131" class="Symbol">(</a><a id="10132" href="simple_essence.html#8466" class="Field">orthonormal</a> <a id="10144" class="Symbol">{</a><a id="10145" class="Argument">f</a> <a id="10147" class="Symbol">=</a> <a id="10149" class="Symbol">(</a><a id="10150" href="simple_essence.html#9890" class="Bound">x</a> <a id="10152" href="simple_essence.html#7988" class="Field Operator">·_</a><a id="10154" class="Symbol">)})</a> <a id="10158" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10178" href="simple_essence.html#9890" class="Bound">x</a>
                <a id="10196" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10197" class="Symbol">})</a>
      <a id="10206" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10208" class="Symbol">λ</a> <a id="10210" class="Symbol">{</a><a id="10211" href="simple_essence.html#10211" class="Bound">lm</a> <a id="10214" class="Symbol">→</a> <a id="10216" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10240" href="simple_essence.html#8984" class="Function">a⊸§←a</a> <a id="10246" class="Symbol">(</a><a id="10247" href="simple_essence.html#8742" class="Function">a⊸§→a</a> <a id="10253" href="simple_essence.html#10211" class="Bound">lm</a><a id="10255" class="Symbol">)</a>
                <a id="10273" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10295" href="simple_essence.html#8984" class="Function">a⊸§←a</a> <a id="10301" class="Symbol">(</a><a id="10302" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10308" class="Symbol">(λ</a> <a id="10311" href="simple_essence.html#10311" class="Bound">acc</a> <a id="10315" href="simple_essence.html#10315" class="Bound">v</a> <a id="10317" class="Symbol">→</a> <a id="10319" href="simple_essence.html#10311" class="Bound">acc</a> <a id="10323" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="10325" class="Symbol">(</a><a id="10326" href="simple_essence.html#7191" class="Field">LinMap.f</a> <a id="10335" href="simple_essence.html#10211" class="Bound">lm</a> <a id="10338" href="simple_essence.html#10315" class="Bound">v</a><a id="10339" class="Symbol">)</a> <a id="10341" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="10343" href="simple_essence.html#10315" class="Bound">v</a><a id="10344" class="Symbol">)</a> <a id="10346" href="simple_essence.html#6224" class="Field">id⊕</a> <a id="10350" href="simple_essence.html#7963" class="Field">basisSet</a><a id="10358" class="Symbol">)</a>
                <a id="10376" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10398" href="simple_essence.html#7174" class="InductiveConstructor">mkLM</a> <a id="10403" class="Symbol">((</a><a id="10405" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10411" class="Symbol">(λ</a> <a id="10414" href="simple_essence.html#10414" class="Bound">acc</a> <a id="10418" href="simple_essence.html#10418" class="Bound">v</a> <a id="10420" class="Symbol">→</a> <a id="10422" href="simple_essence.html#10414" class="Bound">acc</a> <a id="10426" href="simple_essence.html#6237" class="Field Operator">⊕</a> <a id="10428" class="Symbol">(</a><a id="10429" href="simple_essence.html#7191" class="Field">LinMap.f</a> <a id="10438" href="simple_essence.html#10211" class="Bound">lm</a> <a id="10441" href="simple_essence.html#10418" class="Bound">v</a><a id="10442" class="Symbol">)</a> <a id="10444" href="simple_essence.html#6838" class="Field Operator">⊛</a> <a id="10446" href="simple_essence.html#10418" class="Bound">v</a><a id="10447" class="Symbol">)</a> <a id="10449" href="simple_essence.html#6224" class="Field">id⊕</a> <a id="10453" href="simple_essence.html#7963" class="Field">basisSet</a><a id="10461" class="Symbol">)</a><a id="10462" href="simple_essence.html#7988" class="Field Operator">·_</a><a id="10464" class="Symbol">)</a>
                       <a id="10489" href="simple_essence.html#8066" class="Field">·-distrib-⊕</a> <a id="10501" href="simple_essence.html#8198" class="Field">·-comm-⊛</a>
                <a id="10526" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10529" href="simple_essence.html#7509" class="Postulate">⊸≡</a> <a id="10532" class="Symbol">(</a> <a id="10534" href="simple_essence.html#5990" class="Postulate">extensionality</a>
                          <a id="10575" class="Symbol">(</a> <a id="10577" class="Symbol">λ</a> <a id="10579" href="simple_essence.html#10579" class="Bound">x</a> <a id="10581" class="Symbol">→</a> <a id="10583" href="simple_essence.html#8466" class="Field">orthonormal</a> <a id="10595" class="Symbol">{</a><a id="10596" class="Argument">f</a> <a id="10598" class="Symbol">=</a> <a id="10600" href="simple_essence.html#7191" class="Field">LinMap.f</a> <a id="10609" href="simple_essence.html#10211" class="Bound">lm</a><a id="10611" class="Symbol">}</a> <a id="10613" class="Symbol">{</a><a id="10614" class="Argument">x</a> <a id="10616" class="Symbol">=</a> <a id="10618" href="simple_essence.html#10579" class="Bound">x</a><a id="10619" class="Symbol">}</a> <a id="10621" class="Symbol">)</a>
                      <a id="10645" class="Symbol">)</a>
                 <a id="10664" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10684" href="simple_essence.html#10211" class="Bound">lm</a>
                <a id="10703" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10704" class="Symbol">}</a>
      <a id="10712" class="Symbol">)</a>

<a id="10715" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10798" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10860" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="10954" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="11017" class="Comment">--</a>
<a id="11020" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="11043" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="11092" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="11125" class="Comment">--         -------------------------------------</a>
<a id="11174" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11202" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>