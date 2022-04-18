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
{% toc %}

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

<pre class="Agda"><a id="5713" class="Keyword">module</a> <a id="5720" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5735" class="Keyword">where</a>

<a id="5742" class="Keyword">open</a> <a id="5747" class="Keyword">import</a> <a id="5754" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5773" class="Keyword">open</a> <a id="5778" class="Keyword">import</a> <a id="5785" href="Algebra.html" class="Module">Algebra</a>                            <a id="5820" class="Keyword">using</a> <a id="5826" class="Symbol">(</a><a id="5827" href="Algebra.Structures.html#12130" class="Record">IsRing</a><a id="5833" class="Symbol">;</a> <a id="5835" href="Algebra.Structures.html#7016" class="Record">IsNearSemiring</a><a id="5849" class="Symbol">)</a>
<a id="5851" class="Keyword">open</a> <a id="5856" class="Keyword">import</a> <a id="5863" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5898" class="Keyword">using</a> <a id="5904" class="Symbol">(</a><a id="5905" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5919" class="Symbol">)</a>
<a id="5921" class="Keyword">open</a> <a id="5926" class="Keyword">import</a> <a id="5933" href="Data.List.html" class="Module">Data.List</a>
<a id="5943" class="Keyword">open</a> <a id="5948" class="Keyword">import</a> <a id="5955" href="Data.Product.html" class="Module">Data.Product</a> <a id="5968" class="Keyword">using</a> <a id="5974" class="Symbol">(</a><a id="5975" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a><a id="5976" class="Symbol">;</a> <a id="5978" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a><a id="5981" class="Symbol">;</a> <a id="5983" href="Data.Product.html#1369" class="Function">∃</a><a id="5984" class="Symbol">;</a> <a id="5986" href="Data.Product.html#916" class="Function">Σ-syntax</a><a id="5994" class="Symbol">;</a> <a id="5996" href="Data.Product.html#1788" class="Function">∃-syntax</a><a id="6004" class="Symbol">)</a>
<a id="6006" class="Keyword">open</a> <a id="6011" class="Keyword">import</a> <a id="6018" href="Function.html" class="Module">Function</a>     <a id="6031" class="Keyword">using</a> <a id="6037" class="Symbol">(</a><a id="6038" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="6041" class="Symbol">;</a> <a id="6043" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="6046" class="Symbol">;</a> <a id="6048" href="Function.Base.html#615" class="Function">id</a><a id="6050" class="Symbol">;</a> <a id="6052" href="Function.Base.html#636" class="Function">const</a><a id="6057" class="Symbol">)</a>
<a id="6059" class="Keyword">open</a> <a id="6064" class="Keyword">import</a> <a id="6071" href="Level.html" class="Module">Level</a>        <a id="6084" class="Keyword">using</a> <a id="6090" class="Symbol">(</a><a id="6091" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="6096" class="Symbol">;</a> <a id="6098" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="6101" class="Symbol">)</a>

<a id="6104" class="Keyword">import</a> <a id="6111" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="6149" class="Symbol">as</a> <a id="6152" class="Module">Eq</a>
<a id="6155" class="Keyword">open</a> <a id="6160" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="6163" class="Keyword">using</a> <a id="6169" class="Symbol">(</a><a id="6170" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="6173" class="Symbol">;</a> <a id="6175" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="6179" class="Symbol">;</a> <a id="6181" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="6186" class="Symbol">;</a> <a id="6188" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="6191" class="Symbol">;</a> <a id="6193" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="6197" class="Symbol">;</a> <a id="6199" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="6204" class="Symbol">;</a> <a id="6206" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="6214" class="Symbol">;</a> <a id="6216" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="6221" class="Symbol">;</a> <a id="6223" href="Relation.Binary.PropositionalEquality.Core.html#840" class="Function Operator">_≢_</a><a id="6226" class="Symbol">)</a>
<a id="6228" class="Keyword">open</a> <a id="6233" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a>                   <a id="6266" class="Keyword">using</a> <a id="6272" class="Symbol">(</a><a id="6273" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="6279" class="Symbol">;</a> <a id="6281" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="6286" class="Symbol">;</a> <a id="6288" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="6294" class="Symbol">;</a> <a id="6296" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="6298" class="Symbol">)</a>
<a id="6300" class="Keyword">open</a> <a id="6305" class="Keyword">import</a> <a id="6312" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>          <a id="6338" class="Keyword">using</a> <a id="6344" class="Symbol">(</a><a id="6345" href="Relation.Nullary.html#653" class="Function Operator">¬_</a><a id="6347" class="Symbol">)</a>
<a id="6349" class="Keyword">open</a> <a id="6354" class="Keyword">import</a> <a id="6361" href="Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="6387" class="Keyword">using</a> <a id="6393" class="Symbol">(</a><a id="6394" href="Relation.Nullary.Negation.html#929" class="Function">contraposition</a><a id="6408" class="Symbol">)</a>

<a id="6411" class="Keyword">variable</a>
  <a id="6422" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a> <a id="6425" href="simple_essence.html#6425" class="Generalizable">ℓ₂</a> <a id="6428" href="simple_essence.html#6428" class="Generalizable">ℓ₃</a> <a id="6431" class="Symbol">:</a> <a id="6433" href="Agda.Primitive.html#423" class="Postulate">Level</a>
  
<a id="6442" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="6454" href="simple_essence.html#6454" class="Postulate">extensionality</a> <a id="6469" class="Symbol">:</a> <a id="6471" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="6486" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a> <a id="6489" href="simple_essence.html#6425" class="Generalizable">ℓ₂</a>

</pre>
### Type Classes

Here, we define the abstract type classes we'll be using in our proofs.
We use a slight variation on the approach taken in the standard library "bundles", because it yields cleaner, more succinct, abstract code capable of _automatic instance selection_.

**Note:** We've removed our previously defined custom typeclass: `Additive`, in favor of `Ring` defined in the Agda standard library.
We've kept `Scalable`, for now, in order to get some incremental progress working and checked in before attempting to use `Module` and friends.

<pre class="Agda"><a id="7058" class="Keyword">record</a> <a id="Scalable"></a><a id="7065" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="7074" class="Symbol">(</a><a id="7075" href="simple_essence.html#7075" class="Bound">T</a> <a id="7077" class="Symbol">:</a> <a id="7079" class="PrimitiveType">Set</a> <a id="7083" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="7085" class="Symbol">)</a> <a id="7087" class="Symbol">(</a><a id="7088" href="simple_essence.html#7088" class="Bound">A</a> <a id="7090" class="Symbol">:</a> <a id="7092" class="PrimitiveType">Set</a> <a id="7096" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="7098" class="Symbol">)</a> <a id="7100" class="Symbol">:</a> <a id="7102" class="PrimitiveType">Set</a> <a id="7106" class="Symbol">(</a><a id="7107" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="7117" href="simple_essence.html#7083" class="Bound">ℓ₁</a><a id="7119" class="Symbol">)</a> <a id="7121" class="Keyword">where</a>
  <a id="7129" class="Keyword">infix</a> <a id="7135" class="Number">7</a> <a id="7137" href="simple_essence.html#7153" class="Field Operator">_·_</a>
  <a id="7143" class="Keyword">field</a>
    <a id="Scalable._·_"></a><a id="7153" href="simple_essence.html#7153" class="Field Operator">_·_</a> <a id="7157" class="Symbol">:</a> <a id="7159" href="simple_essence.html#7088" class="Bound">A</a> <a id="7161" class="Symbol">→</a> <a id="7163" href="simple_essence.html#7075" class="Bound">T</a> <a id="7165" class="Symbol">→</a> <a id="7167" href="simple_essence.html#7075" class="Bound">T</a>
<a id="7169" class="Keyword">open</a> <a id="7174" href="simple_essence.html#7065" class="Module">Scalable</a> <a id="7183" class="Symbol">⦃</a> <a id="7185" class="Symbol">...</a> <a id="7189" class="Symbol">⦄</a> <a id="7191" class="Keyword">public</a>

<a id="7199" class="Keyword">record</a> <a id="Ring"></a><a id="7206" href="simple_essence.html#7206" class="Record">Ring</a> <a id="7211" class="Symbol">(</a><a id="7212" href="simple_essence.html#7212" class="Bound">A</a> <a id="7214" class="Symbol">:</a> <a id="7216" class="PrimitiveType">Set</a> <a id="7220" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="7222" class="Symbol">)</a> <a id="7224" class="Symbol">:</a> <a id="7226" class="PrimitiveType">Set</a> <a id="7230" class="Symbol">(</a><a id="7231" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="7241" href="simple_essence.html#7220" class="Bound">ℓ₁</a><a id="7243" class="Symbol">)</a> <a id="7245" class="Keyword">where</a>
  <a id="7253" class="Keyword">infixl</a> <a id="7260" class="Number">6</a> <a id="7262" href="simple_essence.html#7307" class="Field Operator">_+_</a>
  <a id="7268" class="Keyword">infixl</a> <a id="7275" class="Number">7</a> <a id="7277" href="simple_essence.html#7327" class="Field Operator">_*_</a>
  <a id="7283" class="Keyword">infix</a>  <a id="7290" class="Number">8</a> <a id="7292" href="simple_essence.html#7347" class="Field Operator">-_</a>
  <a id="7297" class="Keyword">field</a>
    <a id="Ring._+_"></a><a id="7307" href="simple_essence.html#7307" class="Field Operator">_+_</a> <a id="7311" class="Symbol">:</a> <a id="7313" href="simple_essence.html#7212" class="Bound">A</a> <a id="7315" class="Symbol">→</a> <a id="7317" href="simple_essence.html#7212" class="Bound">A</a> <a id="7319" class="Symbol">→</a> <a id="7321" href="simple_essence.html#7212" class="Bound">A</a>
    <a id="Ring._*_"></a><a id="7327" href="simple_essence.html#7327" class="Field Operator">_*_</a> <a id="7331" class="Symbol">:</a> <a id="7333" href="simple_essence.html#7212" class="Bound">A</a> <a id="7335" class="Symbol">→</a> <a id="7337" href="simple_essence.html#7212" class="Bound">A</a> <a id="7339" class="Symbol">→</a> <a id="7341" href="simple_essence.html#7212" class="Bound">A</a>
    <a id="Ring.-_"></a><a id="7347" href="simple_essence.html#7347" class="Field Operator">-_</a>  <a id="7351" class="Symbol">:</a> <a id="7353" href="simple_essence.html#7212" class="Bound">A</a> <a id="7355" class="Symbol">→</a> <a id="7357" href="simple_essence.html#7212" class="Bound">A</a>
    <a id="Ring.𝟘"></a><a id="7363" href="simple_essence.html#7363" class="Field">𝟘</a>   <a id="7367" class="Symbol">:</a> <a id="7369" href="simple_essence.html#7212" class="Bound">A</a>
    <a id="Ring.𝟙"></a><a id="7375" href="simple_essence.html#7375" class="Field">𝟙</a>   <a id="7379" class="Symbol">:</a> <a id="7381" href="simple_essence.html#7212" class="Bound">A</a>
    <a id="7387" class="Symbol">⦃</a> <a id="Ring.isRing"></a><a id="7389" href="simple_essence.html#7389" class="Field">isRing</a> <a id="7396" class="Symbol">⦄</a> <a id="7398" class="Symbol">:</a> <a id="7400" href="Algebra.Structures.html#12130" class="Record">IsRing</a> <a id="7407" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="7411" href="simple_essence.html#7307" class="Field Operator">_+_</a> <a id="7415" href="simple_essence.html#7327" class="Field Operator">_*_</a> <a id="7419" href="simple_essence.html#7347" class="Field Operator">-_</a> <a id="7422" href="simple_essence.html#7363" class="Field">𝟘</a> <a id="7424" href="simple_essence.html#7375" class="Field">𝟙</a>
  <a id="7428" class="Keyword">open</a> <a id="7433" href="Algebra.Structures.html#12130" class="Module">IsRing</a> <a id="7440" href="simple_essence.html#7389" class="Field">isRing</a> <a id="7447" class="Keyword">public</a>
  <a id="7456" class="Keyword">instance</a>
    <a id="Ring.scalableRing"></a><a id="7469" href="simple_essence.html#7469" class="Function">scalableRing</a> <a id="7482" class="Symbol">:</a> <a id="7484" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="7493" href="simple_essence.html#7212" class="Bound">A</a> <a id="7495" href="simple_essence.html#7212" class="Bound">A</a>
    <a id="7501" href="simple_essence.html#7469" class="Function">scalableRing</a> <a id="7514" class="Symbol">=</a> <a id="7516" class="Keyword">record</a>
      <a id="7529" class="Symbol">{</a> <a id="7531" href="simple_essence.html#7153" class="Field Operator">_·_</a> <a id="7535" class="Symbol">=</a> <a id="7537" href="simple_essence.html#7327" class="Field Operator">_*_</a>
      <a id="7547" class="Symbol">}</a>
  <a id="7551" class="Keyword">open</a> <a id="7556" href="simple_essence.html#7065" class="Module">Scalable</a> <a id="7565" href="simple_essence.html#7469" class="Function">scalableRing</a>
<a id="7578" class="Keyword">open</a> <a id="7583" href="simple_essence.html#7206" class="Module">Ring</a> <a id="7588" class="Symbol">⦃</a> <a id="7590" class="Symbol">...</a> <a id="7594" class="Symbol">⦄</a> <a id="7596" class="Keyword">public</a>
    
</pre>
### Linear Maps

Here, we capture our intended meaning of _linearity_.

We take the vector-centric definition offered by Conal in his paper:

> A linear map is one that distributes over _vector_ addition and _scalar_ multiplication.

<pre class="Agda"><a id="7855" class="Keyword">record</a> <a id="LinMap"></a><a id="7862" href="simple_essence.html#7862" class="Record">LinMap</a> <a id="7869" class="Symbol">(</a><a id="7870" href="simple_essence.html#7870" class="Bound">A</a> <a id="7872" class="Symbol">:</a> <a id="7874" class="PrimitiveType">Set</a> <a id="7878" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="7880" class="Symbol">)</a> <a id="7882" class="Symbol">(</a><a id="7883" href="simple_essence.html#7883" class="Bound">B</a> <a id="7885" class="Symbol">:</a> <a id="7887" class="PrimitiveType">Set</a> <a id="7891" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="7893" class="Symbol">)</a> <a id="7895" class="Symbol">{</a><a id="7896" href="simple_essence.html#7896" class="Bound">§</a> <a id="7898" class="Symbol">:</a> <a id="7900" class="PrimitiveType">Set</a> <a id="7904" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="7906" class="Symbol">}</a>
              <a id="7922" class="Symbol">⦃</a> <a id="7924" href="simple_essence.html#7924" class="Bound">_</a> <a id="7926" class="Symbol">:</a> <a id="7928" href="simple_essence.html#7206" class="Record">Ring</a> <a id="7933" href="simple_essence.html#7870" class="Bound">A</a> <a id="7935" class="Symbol">⦄</a> <a id="7937" class="Symbol">⦃</a> <a id="7939" href="simple_essence.html#7939" class="Bound">_</a> <a id="7941" class="Symbol">:</a> <a id="7943" href="simple_essence.html#7206" class="Record">Ring</a> <a id="7948" href="simple_essence.html#7883" class="Bound">B</a> <a id="7950" class="Symbol">⦄</a>
              <a id="7966" class="Symbol">⦃</a> <a id="7968" href="simple_essence.html#7968" class="Bound">_</a> <a id="7970" class="Symbol">:</a> <a id="7972" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="7981" href="simple_essence.html#7870" class="Bound">A</a> <a id="7983" href="simple_essence.html#7896" class="Bound">§</a> <a id="7985" class="Symbol">⦄</a>   <a id="7989" class="Symbol">⦃</a> <a id="7991" href="simple_essence.html#7991" class="Bound">_</a> <a id="7993" class="Symbol">:</a> <a id="7995" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="8004" href="simple_essence.html#7883" class="Bound">B</a> <a id="8006" href="simple_essence.html#7896" class="Bound">§</a> <a id="8008" class="Symbol">⦄</a>
              <a id="8024" class="Symbol">:</a> <a id="8026" class="PrimitiveType">Set</a> <a id="8030" href="simple_essence.html#7878" class="Bound">ℓ₁</a> <a id="8033" class="Keyword">where</a>
  <a id="8041" class="Keyword">constructor</a> <a id="mkLM"></a><a id="8053" href="simple_essence.html#8053" class="InductiveConstructor">mkLM</a>
  <a id="8060" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="8070" href="simple_essence.html#8070" class="Field">f</a>      <a id="8077" class="Symbol">:</a> <a id="8079" href="simple_essence.html#7870" class="Bound">A</a> <a id="8081" class="Symbol">→</a> <a id="8083" href="simple_essence.html#7883" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="8090" href="simple_essence.html#8090" class="Field">adds</a>   <a id="8097" class="Symbol">:</a> <a id="8099" class="Symbol">∀</a> <a id="8101" class="Symbol">{</a><a id="8102" href="simple_essence.html#8102" class="Bound">a</a> <a id="8104" href="simple_essence.html#8104" class="Bound">b</a> <a id="8106" class="Symbol">:</a> <a id="8108" href="simple_essence.html#7870" class="Bound">A</a><a id="8109" class="Symbol">}</a>
             <a id="8124" class="Comment">---------------------</a>
          <a id="8156" class="Symbol">→</a> <a id="8158" href="simple_essence.html#8070" class="Field">f</a> <a id="8160" class="Symbol">(</a><a id="8161" href="simple_essence.html#8102" class="Bound">a</a> <a id="8163" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="8165" href="simple_essence.html#8104" class="Bound">b</a><a id="8166" class="Symbol">)</a> <a id="8168" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8170" href="simple_essence.html#8070" class="Field">f</a> <a id="8172" href="simple_essence.html#8102" class="Bound">a</a> <a id="8174" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="8176" href="simple_essence.html#8070" class="Field">f</a> <a id="8178" href="simple_essence.html#8104" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="8185" href="simple_essence.html#8185" class="Field">scales</a> <a id="8192" class="Symbol">:</a> <a id="8194" class="Symbol">∀</a> <a id="8196" class="Symbol">{</a><a id="8197" href="simple_essence.html#8197" class="Bound">s</a> <a id="8199" class="Symbol">:</a> <a id="8201" href="simple_essence.html#7896" class="Bound">§</a><a id="8202" class="Symbol">}</a> <a id="8204" class="Symbol">{</a><a id="8205" href="simple_essence.html#8205" class="Bound">a</a> <a id="8207" class="Symbol">:</a> <a id="8209" href="simple_essence.html#7870" class="Bound">A</a><a id="8210" class="Symbol">}</a>
             <a id="8225" class="Comment">-------------------</a>
          <a id="8255" class="Symbol">→</a> <a id="8257" href="simple_essence.html#8070" class="Field">f</a> <a id="8259" class="Symbol">(</a><a id="8260" href="simple_essence.html#8197" class="Bound">s</a> <a id="8262" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="8264" href="simple_essence.html#8205" class="Bound">a</a><a id="8265" class="Symbol">)</a> <a id="8267" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8269" href="simple_essence.html#8197" class="Bound">s</a> <a id="8271" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="8273" href="simple_essence.html#8070" class="Field">f</a> <a id="8275" href="simple_essence.html#8205" class="Bound">a</a>

<a id="8278" class="Keyword">open</a> <a id="8283" href="simple_essence.html#7862" class="Module">LinMap</a> <a id="8290" class="Symbol">⦃</a> <a id="8292" class="Symbol">...</a> <a id="8296" class="Symbol">⦄</a> <a id="8298" class="Keyword">public</a>

<a id="8306" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="8332" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="8380" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="8392" href="simple_essence.html#8392" class="Postulate">⊸≡</a> <a id="8395" class="Symbol">:</a> <a id="8397" class="Symbol">{</a><a id="8398" href="simple_essence.html#8398" class="Bound">A</a> <a id="8400" class="Symbol">:</a> <a id="8402" class="PrimitiveType">Set</a> <a id="8406" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="8408" class="Symbol">}</a> <a id="8410" class="Symbol">{</a><a id="8411" href="simple_essence.html#8411" class="Bound">B</a> <a id="8413" class="Symbol">:</a> <a id="8415" class="PrimitiveType">Set</a> <a id="8419" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="8421" class="Symbol">}</a> <a id="8423" class="Symbol">{</a><a id="8424" href="simple_essence.html#8424" class="Bound">§</a> <a id="8426" class="Symbol">:</a> <a id="8428" class="PrimitiveType">Set</a> <a id="8432" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="8434" class="Symbol">}</a>
       <a id="8443" class="Symbol">⦃</a> <a id="8445" href="simple_essence.html#8445" class="Bound">_</a> <a id="8447" class="Symbol">:</a> <a id="8449" href="simple_essence.html#7206" class="Record">Ring</a> <a id="8454" href="simple_essence.html#8398" class="Bound">A</a> <a id="8456" class="Symbol">⦄</a> <a id="8458" class="Symbol">⦃</a> <a id="8460" href="simple_essence.html#8460" class="Bound">_</a> <a id="8462" class="Symbol">:</a> <a id="8464" href="simple_essence.html#7206" class="Record">Ring</a> <a id="8469" href="simple_essence.html#8411" class="Bound">B</a> <a id="8471" class="Symbol">⦄</a>
       <a id="8480" class="Symbol">⦃</a> <a id="8482" href="simple_essence.html#8482" class="Bound">_</a> <a id="8484" class="Symbol">:</a> <a id="8486" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="8495" href="simple_essence.html#8398" class="Bound">A</a> <a id="8497" href="simple_essence.html#8424" class="Bound">§</a> <a id="8499" class="Symbol">⦄</a> <a id="8501" class="Symbol">⦃</a> <a id="8503" href="simple_essence.html#8503" class="Bound">_</a> <a id="8505" class="Symbol">:</a> <a id="8507" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="8516" href="simple_essence.html#8411" class="Bound">B</a> <a id="8518" href="simple_essence.html#8424" class="Bound">§</a> <a id="8520" class="Symbol">⦄</a>
       <a id="8529" class="Symbol">{</a><a id="8530" href="simple_essence.html#8530" class="Bound">lm₁</a> <a id="8534" href="simple_essence.html#8534" class="Bound">lm₂</a> <a id="8538" class="Symbol">:</a> <a id="8540" href="simple_essence.html#7862" class="Record">LinMap</a> <a id="8547" href="simple_essence.html#8398" class="Bound">A</a> <a id="8549" href="simple_essence.html#8411" class="Bound">B</a> <a id="8551" class="Symbol">{</a><a id="8552" href="simple_essence.html#8424" class="Bound">§</a><a id="8553" class="Symbol">}}</a>
    <a id="8560" class="Symbol">→</a> <a id="8562" href="simple_essence.html#8070" class="Field">LinMap.f</a> <a id="8571" href="simple_essence.html#8530" class="Bound">lm₁</a> <a id="8575" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8577" href="simple_essence.html#8070" class="Field">LinMap.f</a> <a id="8586" href="simple_essence.html#8534" class="Bound">lm₂</a>
       <a id="8597" class="Comment">--------------------------</a>
    <a id="8628" class="Symbol">→</a> <a id="8630" href="simple_essence.html#8530" class="Bound">lm₁</a> <a id="8634" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8636" href="simple_essence.html#8534" class="Bound">lm₂</a>

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

<pre class="Agda"><a id="9590" class="Keyword">record</a> <a id="VectorSpace"></a><a id="9597" href="simple_essence.html#9597" class="Record">VectorSpace</a>
  <a id="9611" class="Symbol">(</a><a id="9612" href="simple_essence.html#9612" class="Bound">T</a> <a id="9614" class="Symbol">:</a> <a id="9616" class="PrimitiveType">Set</a> <a id="9620" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="9622" class="Symbol">)</a> <a id="9624" class="Symbol">(</a><a id="9625" href="simple_essence.html#9625" class="Bound">A</a> <a id="9627" class="Symbol">:</a> <a id="9629" class="PrimitiveType">Set</a> <a id="9633" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="9635" class="Symbol">)</a>
  <a id="9639" class="Symbol">⦃</a> <a id="9641" href="simple_essence.html#9641" class="Bound">_</a> <a id="9643" class="Symbol">:</a> <a id="9645" href="simple_essence.html#7206" class="Record">Ring</a> <a id="9650" href="simple_essence.html#9612" class="Bound">T</a> <a id="9652" class="Symbol">⦄</a> <a id="9654" class="Symbol">⦃</a> <a id="9656" href="simple_essence.html#9656" class="Bound">_</a> <a id="9658" class="Symbol">:</a> <a id="9660" href="simple_essence.html#7206" class="Record">Ring</a> <a id="9665" href="simple_essence.html#9625" class="Bound">A</a> <a id="9667" class="Symbol">⦄</a> <a id="9669" class="Symbol">⦃</a> <a id="9671" href="simple_essence.html#9671" class="Bound">_</a> <a id="9673" class="Symbol">:</a> <a id="9675" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="9684" href="simple_essence.html#9612" class="Bound">T</a> <a id="9686" href="simple_essence.html#9625" class="Bound">A</a> <a id="9688" class="Symbol">⦄</a>
  <a id="9692" class="Symbol">:</a> <a id="9694" class="PrimitiveType">Set</a> <a id="9698" class="Symbol">(</a><a id="9699" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="9709" href="simple_essence.html#9620" class="Bound">ℓ₁</a><a id="9711" class="Symbol">)</a> <a id="9713" class="Keyword">where</a>
  <a id="9721" class="Keyword">infix</a>  <a id="9728" class="Number">7</a> <a id="9730" href="simple_essence.html#9812" class="Field Operator">_⊙_</a>
  <a id="9736" class="Keyword">field</a>
    <a id="VectorSpace.I"></a><a id="9746" href="simple_essence.html#9746" class="Field">I</a>     <a id="9752" class="Symbol">:</a> <a id="9754" class="PrimitiveType">Set</a> <a id="9758" href="simple_essence.html#9620" class="Bound">ℓ₁</a>
    <a id="VectorSpace.index"></a><a id="9765" href="simple_essence.html#9765" class="Field">index</a> <a id="9771" class="Symbol">:</a> <a id="9773" href="simple_essence.html#9746" class="Field">I</a> <a id="9775" class="Symbol">→</a> <a id="9777" href="simple_essence.html#9612" class="Bound">T</a> <a id="9779" class="Symbol">→</a> <a id="9781" href="simple_essence.html#9625" class="Bound">A</a>
    <a id="VectorSpace.basisSet"></a><a id="9787" href="simple_essence.html#9787" class="Field">basisSet</a>    <a id="9799" class="Symbol">:</a> <a id="9801" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="9806" href="simple_essence.html#9612" class="Bound">T</a>
    <a id="VectorSpace._⊙_"></a><a id="9812" href="simple_essence.html#9812" class="Field Operator">_⊙_</a>         <a id="9824" class="Symbol">:</a> <a id="9826" href="simple_essence.html#9612" class="Bound">T</a> <a id="9828" class="Symbol">→</a> <a id="9830" href="simple_essence.html#9612" class="Bound">T</a> <a id="9832" class="Symbol">→</a> <a id="9834" href="simple_essence.html#9625" class="Bound">A</a>
    <a id="9840" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.⊙-distrib-+"></a><a id="9890" href="simple_essence.html#9890" class="Field">⊙-distrib-+</a> <a id="9902" class="Symbol">:</a> <a id="9904" class="Symbol">∀</a> <a id="9906" class="Symbol">{</a><a id="9907" href="simple_essence.html#9907" class="Bound">a</a> <a id="9909" href="simple_essence.html#9909" class="Bound">b</a> <a id="9911" href="simple_essence.html#9911" class="Bound">c</a> <a id="9913" class="Symbol">:</a> <a id="9915" href="simple_essence.html#9612" class="Bound">T</a><a id="9916" class="Symbol">}</a>
                  <a id="9936" class="Comment">-------------------------------</a>
               <a id="9983" class="Symbol">→</a> <a id="9985" href="simple_essence.html#9907" class="Bound">a</a> <a id="9987" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="9989" class="Symbol">(</a><a id="9990" href="simple_essence.html#9909" class="Bound">b</a> <a id="9992" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="9994" href="simple_essence.html#9911" class="Bound">c</a><a id="9995" class="Symbol">)</a> <a id="9997" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9999" class="Symbol">(</a><a id="10000" href="simple_essence.html#9907" class="Bound">a</a> <a id="10002" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="10004" href="simple_essence.html#9909" class="Bound">b</a><a id="10005" class="Symbol">)</a> <a id="10007" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="10009" class="Symbol">(</a><a id="10010" href="simple_essence.html#9907" class="Bound">a</a> <a id="10012" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="10014" href="simple_essence.html#9911" class="Bound">c</a><a id="10015" class="Symbol">)</a>
    <a id="VectorSpace.⊙-comm-·"></a><a id="10021" href="simple_essence.html#10021" class="Field">⊙-comm-·</a>    <a id="10033" class="Symbol">:</a> <a id="10035" class="Symbol">∀</a> <a id="10037" class="Symbol">{</a><a id="10038" href="simple_essence.html#10038" class="Bound">s</a> <a id="10040" class="Symbol">:</a> <a id="10042" href="simple_essence.html#9625" class="Bound">A</a><a id="10043" class="Symbol">}</a> <a id="10045" class="Symbol">{</a><a id="10046" href="simple_essence.html#10046" class="Bound">a</a> <a id="10048" href="simple_essence.html#10048" class="Bound">b</a> <a id="10050" class="Symbol">:</a> <a id="10052" href="simple_essence.html#9612" class="Bound">T</a><a id="10053" class="Symbol">}</a>
                  <a id="10073" class="Comment">-------------------------</a>
               <a id="10114" class="Symbol">→</a> <a id="10116" href="simple_essence.html#10046" class="Bound">a</a> <a id="10118" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="10120" class="Symbol">(</a><a id="10121" href="simple_essence.html#10038" class="Bound">s</a> <a id="10123" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="10125" href="simple_essence.html#10048" class="Bound">b</a><a id="10126" class="Symbol">)</a> <a id="10128" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10130" href="simple_essence.html#10038" class="Bound">s</a> <a id="10132" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="10134" class="Symbol">(</a><a id="10135" href="simple_essence.html#10046" class="Bound">a</a> <a id="10137" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="10139" href="simple_essence.html#10048" class="Bound">b</a><a id="10140" class="Symbol">)</a>
    <a id="VectorSpace.orthonormal"></a><a id="10146" href="simple_essence.html#10146" class="Field">orthonormal</a> <a id="10158" class="Symbol">:</a> <a id="10160" class="Symbol">∀</a> <a id="10162" class="Symbol">{</a><a id="10163" href="simple_essence.html#10163" class="Bound">f</a> <a id="10165" class="Symbol">:</a> <a id="10167" href="simple_essence.html#9612" class="Bound">T</a> <a id="10169" class="Symbol">→</a> <a id="10171" href="simple_essence.html#9625" class="Bound">A</a><a id="10172" class="Symbol">}</a>
               <a id="10189" class="Symbol">→</a> <a id="10191" class="Symbol">{</a><a id="10192" href="simple_essence.html#10192" class="Bound">x</a> <a id="10194" class="Symbol">:</a> <a id="10196" href="simple_essence.html#9612" class="Bound">T</a><a id="10197" class="Symbol">}</a>
                  <a id="10217" class="Comment">------------------------------------</a>
               <a id="10269" class="Symbol">→</a> <a id="10271" class="Symbol">(</a> <a id="10273" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10279" class="Symbol">(λ</a> <a id="10282" href="simple_essence.html#10282" class="Bound">acc</a> <a id="10286" href="simple_essence.html#10286" class="Bound">v</a> <a id="10288" class="Symbol">→</a> <a id="10290" href="simple_essence.html#10282" class="Bound">acc</a> <a id="10294" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="10296" class="Symbol">(</a><a id="10297" href="simple_essence.html#10163" class="Bound">f</a> <a id="10299" href="simple_essence.html#10286" class="Bound">v</a><a id="10300" class="Symbol">)</a> <a id="10302" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="10304" href="simple_essence.html#10286" class="Bound">v</a><a id="10305" class="Symbol">)</a>
                          <a id="10333" href="simple_essence.html#7363" class="Field">𝟘</a> <a id="10335" href="simple_essence.html#9787" class="Field">basisSet</a>
                  <a id="10362" class="Symbol">)</a> <a id="10364" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="10366" href="simple_essence.html#10192" class="Bound">x</a> <a id="10368" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10370" href="simple_essence.html#10163" class="Bound">f</a> <a id="10372" href="simple_essence.html#10192" class="Bound">x</a>
<a id="10374" class="Keyword">open</a> <a id="10379" href="simple_essence.html#9597" class="Module">VectorSpace</a> <a id="10391" class="Symbol">⦃</a> <a id="10393" class="Symbol">...</a> <a id="10397" class="Symbol">⦄</a> <a id="10399" class="Keyword">public</a>

</pre>
### Isomorphism 1: `(A ⊸ s) ↔ A`

Here, I prove that a linear map from some "vector" type `T` to a scalar of its _carrier_ type `A` is isomorphic to `T`.

<pre class="Agda"><a id="a⊸§→a"></a><a id="10575" href="simple_essence.html#10575" class="Function">a⊸§→a</a> <a id="10581" class="Symbol">:</a> <a id="10583" class="Symbol">{</a><a id="10584" href="simple_essence.html#10584" class="Bound">T</a> <a id="10586" class="Symbol">:</a> <a id="10588" class="PrimitiveType">Set</a> <a id="10592" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="10594" class="Symbol">}</a> <a id="10596" class="Symbol">{</a><a id="10597" href="simple_essence.html#10597" class="Bound">A</a> <a id="10599" class="Symbol">:</a> <a id="10601" class="PrimitiveType">Set</a> <a id="10605" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="10607" class="Symbol">}</a>
         <a id="10618" class="Symbol">⦃</a> <a id="10620" href="simple_essence.html#10620" class="Bound">_</a> <a id="10622" class="Symbol">:</a> <a id="10624" href="simple_essence.html#7206" class="Record">Ring</a> <a id="10629" href="simple_essence.html#10584" class="Bound">T</a> <a id="10631" class="Symbol">⦄</a> <a id="10633" class="Symbol">⦃</a> <a id="10635" href="simple_essence.html#10635" class="Bound">_</a> <a id="10637" class="Symbol">:</a> <a id="10639" href="simple_essence.html#7206" class="Record">Ring</a> <a id="10644" href="simple_essence.html#10597" class="Bound">A</a> <a id="10646" class="Symbol">⦄</a>
         <a id="10657" class="Symbol">⦃</a> <a id="10659" href="simple_essence.html#10659" class="Bound">_</a> <a id="10661" class="Symbol">:</a> <a id="10663" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="10672" href="simple_essence.html#10584" class="Bound">T</a> <a id="10674" href="simple_essence.html#10597" class="Bound">A</a> <a id="10676" class="Symbol">⦄</a>
         <a id="10687" class="Symbol">⦃</a> <a id="10689" href="simple_essence.html#10689" class="Bound">_</a> <a id="10691" class="Symbol">:</a> <a id="10693" href="simple_essence.html#9597" class="Record">VectorSpace</a> <a id="10705" href="simple_essence.html#10584" class="Bound">T</a> <a id="10707" href="simple_essence.html#10597" class="Bound">A</a> <a id="10709" class="Symbol">⦄</a>
         <a id="10720" class="Comment">------------------------------</a>
      <a id="10757" class="Symbol">→</a> <a id="10759" href="simple_essence.html#7862" class="Record">LinMap</a> <a id="10766" href="simple_essence.html#10584" class="Bound">T</a> <a id="10768" href="simple_essence.html#10597" class="Bound">A</a> <a id="10770" class="Symbol">{</a><a id="10771" href="simple_essence.html#10597" class="Bound">A</a><a id="10772" class="Symbol">}</a> <a id="10774" class="Symbol">→</a> <a id="10776" href="simple_essence.html#10584" class="Bound">T</a>
<a id="10778" href="simple_essence.html#10575" class="Function">a⊸§→a</a> <a id="10784" class="Symbol">=</a> <a id="10786" class="Symbol">λ</a> <a id="10788" class="Symbol">{</a> <a id="10790" href="simple_essence.html#10790" class="Bound">lm</a> <a id="10793" class="Symbol">→</a> <a id="10795" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10801" class="Symbol">(λ</a> <a id="10804" href="simple_essence.html#10804" class="Bound">acc</a> <a id="10808" href="simple_essence.html#10808" class="Bound">v</a> <a id="10810" class="Symbol">→</a>
                     <a id="10833" href="simple_essence.html#10804" class="Bound">acc</a> <a id="10837" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="10839" class="Symbol">(</a><a id="10840" href="simple_essence.html#8070" class="Field">LinMap.f</a> <a id="10849" href="simple_essence.html#10790" class="Bound">lm</a> <a id="10852" href="simple_essence.html#10808" class="Bound">v</a><a id="10853" class="Symbol">)</a> <a id="10855" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="10857" href="simple_essence.html#10808" class="Bound">v</a><a id="10858" class="Symbol">)</a> <a id="10860" href="simple_essence.html#7363" class="Field">𝟘</a> <a id="10862" href="simple_essence.html#9787" class="Field">basisSet</a> <a id="10871" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="10874" href="simple_essence.html#10874" class="Function">a⊸§←a</a> <a id="10880" class="Symbol">:</a> <a id="10882" class="Symbol">{</a><a id="10883" href="simple_essence.html#10883" class="Bound">T</a> <a id="10885" class="Symbol">:</a> <a id="10887" class="PrimitiveType">Set</a> <a id="10891" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="10893" class="Symbol">}</a> <a id="10895" class="Symbol">{</a><a id="10896" href="simple_essence.html#10896" class="Bound">A</a> <a id="10898" class="Symbol">:</a> <a id="10900" class="PrimitiveType">Set</a> <a id="10904" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="10906" class="Symbol">}</a>
         <a id="10917" class="Symbol">⦃</a> <a id="10919" href="simple_essence.html#10919" class="Bound">_</a> <a id="10921" class="Symbol">:</a> <a id="10923" href="simple_essence.html#7206" class="Record">Ring</a> <a id="10928" href="simple_essence.html#10883" class="Bound">T</a> <a id="10930" class="Symbol">⦄</a> <a id="10932" class="Symbol">⦃</a> <a id="10934" href="simple_essence.html#10934" class="Bound">_</a> <a id="10936" class="Symbol">:</a> <a id="10938" href="simple_essence.html#7206" class="Record">Ring</a> <a id="10943" href="simple_essence.html#10896" class="Bound">A</a> <a id="10945" class="Symbol">⦄</a>
         <a id="10956" class="Symbol">⦃</a> <a id="10958" href="simple_essence.html#10958" class="Bound">_</a> <a id="10960" class="Symbol">:</a> <a id="10962" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="10971" href="simple_essence.html#10883" class="Bound">T</a> <a id="10973" href="simple_essence.html#10896" class="Bound">A</a> <a id="10975" class="Symbol">⦄</a>
         <a id="10986" class="Symbol">⦃</a> <a id="10988" href="simple_essence.html#10988" class="Bound">_</a> <a id="10990" class="Symbol">:</a> <a id="10992" href="simple_essence.html#9597" class="Record">VectorSpace</a> <a id="11004" href="simple_essence.html#10883" class="Bound">T</a> <a id="11006" href="simple_essence.html#10896" class="Bound">A</a> <a id="11008" class="Symbol">⦄</a>
         <a id="11019" class="Comment">--------------------------------------</a>
      <a id="11064" class="Symbol">→</a> <a id="11066" href="simple_essence.html#10883" class="Bound">T</a> <a id="11068" class="Symbol">→</a> <a id="11070" href="simple_essence.html#7862" class="Record">LinMap</a> <a id="11077" href="simple_essence.html#10883" class="Bound">T</a> <a id="11079" href="simple_essence.html#10896" class="Bound">A</a> <a id="11081" class="Symbol">{</a><a id="11082" href="simple_essence.html#10896" class="Bound">A</a><a id="11083" class="Symbol">}</a>
<a id="11085" href="simple_essence.html#10874" class="Function">a⊸§←a</a> <a id="11091" class="Symbol">=</a> <a id="11093" class="Symbol">λ</a> <a id="11095" class="Symbol">{</a> <a id="11097" href="simple_essence.html#11097" class="Bound">a</a> <a id="11099" class="Symbol">→</a> <a id="11101" href="simple_essence.html#8053" class="InductiveConstructor">mkLM</a> <a id="11106" class="Symbol">(</a><a id="11107" href="simple_essence.html#11097" class="Bound">a</a> <a id="11109" href="simple_essence.html#9812" class="Field Operator">⊙_</a><a id="11111" class="Symbol">)</a> <a id="11113" href="simple_essence.html#9890" class="Field">⊙-distrib-+</a> <a id="11125" href="simple_essence.html#10021" class="Field">⊙-comm-·</a> <a id="11134" class="Symbol">}</a>

<a id="11137" class="Comment">-- Danger, Will Robinson!</a>
<a id="11163" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="11175" href="simple_essence.html#11175" class="Postulate">x·z≡y·z→x≡y</a> <a id="11187" class="Symbol">:</a> <a id="11189" class="Symbol">{</a><a id="11190" href="simple_essence.html#11190" class="Bound">T</a> <a id="11192" class="Symbol">:</a> <a id="11194" class="PrimitiveType">Set</a> <a id="11198" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="11200" class="Symbol">}</a> <a id="11202" class="Symbol">{</a><a id="11203" href="simple_essence.html#11203" class="Bound">A</a> <a id="11205" class="Symbol">:</a> <a id="11207" class="PrimitiveType">Set</a> <a id="11211" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="11213" class="Symbol">}</a>
                 <a id="11232" class="Symbol">⦃</a> <a id="11234" href="simple_essence.html#11234" class="Bound">_</a> <a id="11236" class="Symbol">:</a> <a id="11238" href="simple_essence.html#7206" class="Record">Ring</a> <a id="11243" href="simple_essence.html#11190" class="Bound">T</a> <a id="11245" class="Symbol">⦄</a> <a id="11247" class="Symbol">⦃</a> <a id="11249" href="simple_essence.html#11249" class="Bound">_</a> <a id="11251" class="Symbol">:</a> <a id="11253" href="simple_essence.html#7206" class="Record">Ring</a> <a id="11258" href="simple_essence.html#11203" class="Bound">A</a> <a id="11260" class="Symbol">⦄</a>
                 <a id="11279" class="Symbol">⦃</a> <a id="11281" href="simple_essence.html#11281" class="Bound">_</a> <a id="11283" class="Symbol">:</a> <a id="11285" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="11294" href="simple_essence.html#11190" class="Bound">T</a> <a id="11296" href="simple_essence.html#11203" class="Bound">A</a> <a id="11298" class="Symbol">⦄</a> <a id="11300" class="Symbol">⦃</a> <a id="11302" href="simple_essence.html#11302" class="Bound">_</a> <a id="11304" class="Symbol">:</a> <a id="11306" href="simple_essence.html#9597" class="Record">VectorSpace</a> <a id="11318" href="simple_essence.html#11190" class="Bound">T</a> <a id="11320" href="simple_essence.html#11203" class="Bound">A</a> <a id="11322" class="Symbol">⦄</a>
                 <a id="11341" class="Symbol">{</a><a id="11342" href="simple_essence.html#11342" class="Bound">x</a> <a id="11344" href="simple_essence.html#11344" class="Bound">y</a> <a id="11346" class="Symbol">:</a> <a id="11348" href="simple_essence.html#11190" class="Bound">T</a><a id="11349" class="Symbol">}</a>
              <a id="11365" class="Symbol">→</a> <a id="11367" class="Symbol">(∀</a> <a id="11370" class="Symbol">{</a><a id="11371" href="simple_essence.html#11371" class="Bound">z</a> <a id="11373" class="Symbol">:</a> <a id="11375" href="simple_essence.html#11190" class="Bound">T</a><a id="11376" class="Symbol">}</a> <a id="11378" class="Symbol">→</a> <a id="11380" href="simple_essence.html#11342" class="Bound">x</a> <a id="11382" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="11384" href="simple_essence.html#11371" class="Bound">z</a> <a id="11386" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11388" href="simple_essence.html#11344" class="Bound">y</a> <a id="11390" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="11392" href="simple_essence.html#11371" class="Bound">z</a><a id="11393" class="Symbol">)</a>
                 <a id="11412" class="Comment">---------------------------------------------</a>
              <a id="11472" class="Symbol">→</a> <a id="11474" href="simple_essence.html#11342" class="Bound">x</a> <a id="11476" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11478" href="simple_essence.html#11344" class="Bound">y</a>
<a id="11480" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="11540" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="11607" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="11638" href="simple_essence.html#11638" class="Function">a⊸§↔a</a> <a id="11644" class="Symbol">:</a> <a id="11646" class="Symbol">{</a><a id="11647" href="simple_essence.html#11647" class="Bound">T</a> <a id="11649" class="Symbol">:</a> <a id="11651" class="PrimitiveType">Set</a> <a id="11655" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="11657" class="Symbol">}</a> <a id="11659" class="Symbol">{</a><a id="11660" href="simple_essence.html#11660" class="Bound">A</a> <a id="11662" class="Symbol">:</a> <a id="11664" class="PrimitiveType">Set</a> <a id="11668" href="simple_essence.html#6422" class="Generalizable">ℓ₁</a><a id="11670" class="Symbol">}</a>
         <a id="11681" class="Symbol">⦃</a> <a id="11683" href="simple_essence.html#11683" class="Bound">_</a> <a id="11685" class="Symbol">:</a> <a id="11687" href="simple_essence.html#7206" class="Record">Ring</a> <a id="11692" href="simple_essence.html#11647" class="Bound">T</a> <a id="11694" class="Symbol">⦄</a> <a id="11696" class="Symbol">⦃</a> <a id="11698" href="simple_essence.html#11698" class="Bound">_</a> <a id="11700" class="Symbol">:</a> <a id="11702" href="simple_essence.html#7206" class="Record">Ring</a> <a id="11707" href="simple_essence.html#11660" class="Bound">A</a> <a id="11709" class="Symbol">⦄</a>
         <a id="11720" class="Symbol">⦃</a> <a id="11722" href="simple_essence.html#11722" class="Bound">_</a> <a id="11724" class="Symbol">:</a> <a id="11726" href="simple_essence.html#7065" class="Record">Scalable</a> <a id="11735" href="simple_essence.html#11647" class="Bound">T</a> <a id="11737" href="simple_essence.html#11660" class="Bound">A</a> <a id="11739" class="Symbol">⦄</a> <a id="11741" class="Symbol">⦃</a> <a id="11743" href="simple_essence.html#11743" class="Bound">_</a> <a id="11745" class="Symbol">:</a> <a id="11747" href="simple_essence.html#9597" class="Record">VectorSpace</a> <a id="11759" href="simple_essence.html#11647" class="Bound">T</a> <a id="11761" href="simple_essence.html#11660" class="Bound">A</a> <a id="11763" class="Symbol">⦄</a>
         <a id="11774" class="Comment">---------------------------------------------</a>
      <a id="11826" class="Symbol">→</a> <a id="11828" class="Symbol">(</a><a id="11829" href="simple_essence.html#7862" class="Record">LinMap</a> <a id="11836" href="simple_essence.html#11647" class="Bound">T</a> <a id="11838" href="simple_essence.html#11660" class="Bound">A</a><a id="11839" class="Symbol">)</a> <a id="11841" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="11843" href="simple_essence.html#11647" class="Bound">T</a>
<a id="11845" href="simple_essence.html#11638" class="Function">a⊸§↔a</a> <a id="11851" class="Symbol">=</a>
  <a id="11855" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="11859" class="Symbol">{</a><a id="11860" class="Argument">f</a> <a id="11862" class="Symbol">=</a> <a id="11864" href="simple_essence.html#10575" class="Function">a⊸§→a</a><a id="11869" class="Symbol">}</a> <a id="11871" class="Symbol">{</a><a id="11872" class="Argument">f⁻¹</a> <a id="11876" class="Symbol">=</a> <a id="11878" href="simple_essence.html#10874" class="Function">a⊸§←a</a><a id="11883" class="Symbol">}</a>
      <a id="11891" class="Symbol">(</a> <a id="11893" class="Symbol">(λ</a> <a id="11896" class="Symbol">{</a><a id="11897" href="simple_essence.html#11897" class="Bound">x</a> <a id="11899" class="Symbol">→</a> <a id="11901" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="11925" href="simple_essence.html#10575" class="Function">a⊸§→a</a> <a id="11931" class="Symbol">(</a><a id="11932" href="simple_essence.html#10874" class="Function">a⊸§←a</a> <a id="11938" href="simple_essence.html#11897" class="Bound">x</a><a id="11939" class="Symbol">)</a>
                <a id="11957" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="11979" href="simple_essence.html#10575" class="Function">a⊸§→a</a> <a id="11985" class="Symbol">(</a><a id="11986" href="simple_essence.html#8053" class="InductiveConstructor">mkLM</a> <a id="11991" class="Symbol">(</a><a id="11992" href="simple_essence.html#11897" class="Bound">x</a> <a id="11994" href="simple_essence.html#9812" class="Field Operator">⊙_</a><a id="11996" class="Symbol">)</a> <a id="11998" href="simple_essence.html#9890" class="Field">⊙-distrib-+</a> <a id="12010" href="simple_essence.html#10021" class="Field">⊙-comm-·</a><a id="12018" class="Symbol">)</a>
                <a id="12036" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="12058" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12064" class="Symbol">(λ</a> <a id="12067" href="simple_essence.html#12067" class="Bound">acc</a> <a id="12071" href="simple_essence.html#12071" class="Bound">v</a> <a id="12073" class="Symbol">→</a> <a id="12075" href="simple_essence.html#12067" class="Bound">acc</a> <a id="12079" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="12081" class="Symbol">(</a><a id="12082" href="simple_essence.html#11897" class="Bound">x</a> <a id="12084" href="simple_essence.html#9812" class="Field Operator">⊙</a> <a id="12086" href="simple_essence.html#12071" class="Bound">v</a><a id="12087" class="Symbol">)</a> <a id="12089" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="12091" href="simple_essence.html#12071" class="Bound">v</a><a id="12092" class="Symbol">)</a> <a id="12094" href="simple_essence.html#7363" class="Field">𝟘</a> <a id="12096" href="simple_essence.html#9787" class="Field">basisSet</a>
                <a id="12121" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12124" href="simple_essence.html#11175" class="Postulate">x·z≡y·z→x≡y</a> <a id="12136" href="simple_essence.html#10146" class="Field">orthonormal</a> <a id="12148" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="12168" href="simple_essence.html#11897" class="Bound">x</a>
                <a id="12186" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12187" class="Symbol">})</a>
      <a id="12196" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="12198" class="Symbol">λ</a> <a id="12200" class="Symbol">{</a><a id="12201" href="simple_essence.html#12201" class="Bound">lm</a> <a id="12204" class="Symbol">→</a> <a id="12206" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                    <a id="12232" href="simple_essence.html#10874" class="Function">a⊸§←a</a> <a id="12238" class="Symbol">(</a><a id="12239" href="simple_essence.html#10575" class="Function">a⊸§→a</a> <a id="12245" href="simple_essence.html#12201" class="Bound">lm</a><a id="12247" class="Symbol">)</a>
                  <a id="12267" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12291" href="simple_essence.html#10874" class="Function">a⊸§←a</a> <a id="12297" class="Symbol">(</a><a id="12298" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12304" class="Symbol">(λ</a> <a id="12307" href="simple_essence.html#12307" class="Bound">acc</a> <a id="12311" href="simple_essence.html#12311" class="Bound">v</a> <a id="12313" class="Symbol">→</a>
                                     <a id="12352" href="simple_essence.html#12307" class="Bound">acc</a> <a id="12356" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="12358" class="Symbol">(</a><a id="12359" href="simple_essence.html#8070" class="Field">LinMap.f</a> <a id="12368" href="simple_essence.html#12201" class="Bound">lm</a> <a id="12371" href="simple_essence.html#12311" class="Bound">v</a><a id="12372" class="Symbol">)</a> <a id="12374" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="12376" href="simple_essence.html#12311" class="Bound">v</a><a id="12377" class="Symbol">)</a> <a id="12379" href="simple_essence.html#7363" class="Field">𝟘</a> <a id="12381" href="simple_essence.html#9787" class="Field">basisSet</a><a id="12389" class="Symbol">)</a>
                  <a id="12409" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12433" href="simple_essence.html#8053" class="InductiveConstructor">mkLM</a> <a id="12438" class="Symbol">(</a> <a id="12440" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12446" class="Symbol">(</a> <a id="12448" class="Symbol">λ</a> <a id="12450" href="simple_essence.html#12450" class="Bound">acc</a> <a id="12454" href="simple_essence.html#12454" class="Bound">v</a> <a id="12456" class="Symbol">→</a>
                                     <a id="12495" href="simple_essence.html#12450" class="Bound">acc</a> <a id="12499" href="simple_essence.html#7307" class="Field Operator">+</a> <a id="12501" class="Symbol">(</a><a id="12502" href="simple_essence.html#8070" class="Field">LinMap.f</a> <a id="12511" href="simple_essence.html#12201" class="Bound">lm</a> <a id="12514" href="simple_essence.html#12454" class="Bound">v</a><a id="12515" class="Symbol">)</a> <a id="12517" href="simple_essence.html#7153" class="Field Operator">·</a> <a id="12519" href="simple_essence.html#12454" class="Bound">v</a>
                                 <a id="12554" class="Symbol">)</a> <a id="12556" href="simple_essence.html#7363" class="Field">𝟘</a> <a id="12558" href="simple_essence.html#9787" class="Field">basisSet</a>
                           <a id="12594" href="simple_essence.html#9812" class="Field Operator">⊙_</a>
                         <a id="12622" class="Symbol">)</a> <a id="12624" href="simple_essence.html#9890" class="Field">⊙-distrib-+</a> <a id="12636" href="simple_essence.html#10021" class="Field">⊙-comm-·</a>
                  <a id="12663" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12666" href="simple_essence.html#8392" class="Postulate">⊸≡</a> <a id="12669" class="Symbol">(</a> <a id="12671" href="simple_essence.html#6454" class="Postulate">extensionality</a>
                            <a id="12714" class="Symbol">(</a> <a id="12716" class="Symbol">λ</a> <a id="12718" href="simple_essence.html#12718" class="Bound">x</a> <a id="12720" class="Symbol">→</a> <a id="12722" href="simple_essence.html#10146" class="Field">orthonormal</a> <a id="12734" class="Symbol">{</a><a id="12735" class="Argument">f</a> <a id="12737" class="Symbol">=</a> <a id="12739" href="simple_essence.html#8070" class="Field">LinMap.f</a> <a id="12748" href="simple_essence.html#12201" class="Bound">lm</a><a id="12750" class="Symbol">}</a> <a id="12752" class="Symbol">{</a><a id="12753" class="Argument">x</a> <a id="12755" class="Symbol">=</a> <a id="12757" href="simple_essence.html#12718" class="Bound">x</a><a id="12758" class="Symbol">}</a> <a id="12760" class="Symbol">)</a>
                        <a id="12786" class="Symbol">)</a>
                   <a id="12807" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                    <a id="12829" href="simple_essence.html#12201" class="Bound">lm</a>
                  <a id="12850" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12851" class="Symbol">}</a>
      <a id="12859" class="Symbol">)</a>

</pre>
### Stashed

Stashed coding attempts.

<pre class="Agda"><a id="12914" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="12997" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="13059" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="13153" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="13216" class="Comment">--</a>
<a id="13219" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="13242" class="Comment">--         ⦃_ : Additive A⦄ ⦃_ : Scalable A⦄</a>
<a id="13287" class="Comment">--         ⦃_ : VectorSpace A⦄</a>
<a id="13318" class="Comment">--         -------------------------------------</a>
<a id="13367" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="13395" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

<a id="13427" class="Comment">-- -- f(0) = 0</a>
<a id="13442" class="Comment">-- zero-lin : {A B : Set a}</a>
<a id="13470" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13521" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13572" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>

<a id="13605" class="Comment">-- -- Injectivity of linear function</a>
<a id="13642" class="Comment">-- inj-lin : {A B : Set a} {x y : A}</a>
<a id="13679" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13730" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13781" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>
<a id="13813" class="Comment">--        → LinMap.f _ x ≡ LinMap.f _ y</a>
<a id="13853" class="Comment">--           ---------------------------</a>
<a id="13894" class="Comment">--        → x ≡ y</a>
<a id="13912" class="Comment">-- inj-lin {x = x} {y = y} fx≡fy =</a>
<a id="13947" class="Comment">--   let f = LinMap.f _</a>
<a id="13971" class="Comment">--    in begin</a>
<a id="13986" class="Comment">--         x</a>
<a id="13999" class="Comment">--       ≡⟨⟩</a>
<a id="14012" class="Comment">--         f (x - y)</a>
<a id="14033" class="Comment">--       ≡⟨ LinMap.adds _ ⟩</a>
<a id="14061" class="Comment">--         f x - f y</a>
<a id="14082" class="Comment">--       ≡⟨ sub-≡ fx≡fy ⟩</a>
<a id="14108" class="Comment">--         0</a>
<a id="14121" class="Comment">--       ≡⟨⟩</a>
<a id="14134" class="Comment">--         y</a>
<a id="14147" class="Comment">--       ∎</a>
      
<a id="14165" class="Comment">-- cong-app′ : ∀ {A : Set a} {B : Set b} {f : A → B} {x y : A}</a>
<a id="14228" class="Comment">--          → f x ≡ f y</a>
<a id="14252" class="Comment">--             ---------</a>
<a id="14277" class="Comment">--          → x ≡ y</a>
<a id="14297" class="Comment">-- cong-app′ fx≡fy = {!contraposition!}</a>
         
<a id="14347" class="Comment">-- x·z≡y·z→x≡y : {A : Set a}</a>
<a id="14376" class="Comment">--                ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="14432" class="Comment">--                ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="14491" class="Comment">--                {x y : A}</a>
<a id="14519" class="Comment">--             → (∀ {z : A} → x · z ≡ y · z)</a>
<a id="14564" class="Comment">--                ------------------------------------------------------------</a>
<a id="14643" class="Comment">--             → x ≡ y</a>
<a id="14666" class="Comment">-- x·z≡y·z→x≡y {x = x} {y = y} g =</a>
<a id="14701" class="Comment">--   let f = LinMap.f _</a>
<a id="14725" class="Comment">--       z = foldl (λ acc v → acc ⊕ f v ⊛ v) id⊕ basisSet</a>
<a id="14783" class="Comment">--       x·z≡y·z = g {z}</a>
<a id="14808" class="Comment">--    in cong-app refl {!!}</a>
<a id="14836" class="Comment">--    -- in begin</a>
<a id="14854" class="Comment">--    --      -- ?</a>
<a id="14873" class="Comment">--    --      x·z≡y·z</a>
<a id="14895" class="Comment">--    --    -- ≡⟨ ? ⟩</a>
<a id="14917" class="Comment">--    --    --   x · z ≡ y · z</a>
<a id="14948" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="14967" class="Comment">--    --    -- ≡⟨ cong (_≡ y · z) comm-· ⟩</a>
<a id="15010" class="Comment">--    --      z · x ≡ y · z</a>
<a id="15038" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15057" class="Comment">--    --    -- ≡⟨ cong (z · x ≡_) comm-· ⟩</a>
<a id="15100" class="Comment">--    --      z · x ≡ z · y</a>
<a id="15128" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15147" class="Comment">--    --    -- ≡⟨ cong (_≡ z · y) (orthonormal) ⟩</a>
<a id="15197" class="Comment">--    --      f x ≡ z · y</a>
<a id="15223" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15242" class="Comment">--    --    -- ≡⟨ cong (f x ≡_) (orthonormal) ⟩</a>
<a id="15290" class="Comment">--    --      f x ≡ f y</a>
<a id="15314" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15333" class="Comment">--    --    -- ≡⟨ cong-app ⟩</a>
<a id="15362" class="Comment">--    --      x ≡ y</a>
<a id="15382" class="Comment">--    --    ∎</a>

<a id="15397" class="Comment">-- -- So, how was Agsy able to jump over all of that?</a>
<a id="15451" class="Comment">-- -- My usual experience w/ Agsy is that when I ask it to solve anything</a>
<a id="15525" class="Comment">-- -- non-trivial by itself it always complains, &quot;Sorry, I don&#39;t support</a>
<a id="15598" class="Comment">-- -- literals, yet.&quot;, which I&#39;ve never understood.</a>

<a id="15651" class="Comment">-- a⊸§↔a : {A : Set a}</a>
<a id="15674" class="Comment">--          ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="15724" class="Comment">--          ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="15777" class="Comment">--          -----------------------------------------</a>
<a id="15831" class="Comment">--       → (LinMap A §) ↔ A</a>
<a id="15859" class="Comment">-- a⊸§↔a {A} =</a>
<a id="15874" class="Comment">--   mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}</a>
<a id="15909" class="Comment">--       ( (λ {x → begin</a>
<a id="15934" class="Comment">--                   a⊸§→a (a⊸§←a x)</a>
<a id="15971" class="Comment">--                 ≡⟨⟩</a>
<a id="15994" class="Comment">--                   a⊸§→a (mkLM (x ·_) ·-distrib-⊕ ·-comm-⊛)</a>
<a id="16056" class="Comment">--                 ≡⟨⟩</a>
<a id="16079" class="Comment">--                   foldl (λ acc v → acc ⊕ (x · v) ⊛ v) id⊕ basisSet</a>
<a id="16149" class="Comment">--                 ≡⟨ x·z≡y·z→x≡y (orthonormal {f = (x ·_)}) ⟩</a>
<a id="16212" class="Comment">--                   x</a>
<a id="16235" class="Comment">--                 ∎})</a>
<a id="16258" class="Comment">--       , λ {lm → begin</a>
<a id="16283" class="Comment">--                   a⊸§←a (a⊸§→a lm)</a>
<a id="16321" class="Comment">--                 ≡⟨⟩</a>
<a id="16344" class="Comment">--                   a⊸§←a (foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)</a>
<a id="16430" class="Comment">--                 ≡⟨⟩</a>
<a id="16453" class="Comment">--                   mkLM ((foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)·_)</a>
<a id="16542" class="Comment">--                        ·-distrib-⊕ ·-comm-⊛</a>
<a id="16589" class="Comment">--                 ≡⟨ ⊸≡ ( extensionality</a>
<a id="16631" class="Comment">--                           ( λ x → orthonormal {f = LinMap.f lm} {x = x} )</a>
<a id="16708" class="Comment">--                       )</a>
<a id="16735" class="Comment">--                  ⟩</a>
<a id="16757" class="Comment">--                   lm</a>
<a id="16781" class="Comment">--                 ∎}</a>
<a id="16803" class="Comment">--       )</a>


</pre>