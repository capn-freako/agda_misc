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

<pre class="Agda"><a id="5703" class="Keyword">module</a> <a id="5710" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5725" class="Keyword">where</a>

<a id="5732" class="Keyword">open</a> <a id="5737" class="Keyword">import</a> <a id="5744" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5763" class="Keyword">open</a> <a id="5768" class="Keyword">import</a> <a id="5775" href="Algebra.html" class="Module">Algebra</a>                            <a id="5810" class="Keyword">using</a> <a id="5816" class="Symbol">(</a><a id="5817" href="Algebra.Structures.html#12130" class="Record">IsRing</a><a id="5823" class="Symbol">;</a> <a id="5825" href="Algebra.Structures.html#7016" class="Record">IsNearSemiring</a><a id="5839" class="Symbol">)</a>
<a id="5841" class="Keyword">open</a> <a id="5846" class="Keyword">import</a> <a id="5853" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5888" class="Keyword">using</a> <a id="5894" class="Symbol">(</a><a id="5895" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5909" class="Symbol">)</a>
<a id="5911" class="Keyword">open</a> <a id="5916" class="Keyword">import</a> <a id="5923" href="Data.List.html" class="Module">Data.List</a>
<a id="5933" class="Keyword">open</a> <a id="5938" class="Keyword">import</a> <a id="5945" href="Data.Product.html" class="Module">Data.Product</a> <a id="5958" class="Keyword">using</a> <a id="5964" class="Symbol">(</a><a id="5965" href="Agda.Builtin.Sigma.html#166" class="Record">Σ</a><a id="5966" class="Symbol">;</a> <a id="5968" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">_,_</a><a id="5971" class="Symbol">;</a> <a id="5973" href="Data.Product.html#1369" class="Function">∃</a><a id="5974" class="Symbol">;</a> <a id="5976" href="Data.Product.html#916" class="Function">Σ-syntax</a><a id="5984" class="Symbol">;</a> <a id="5986" href="Data.Product.html#1788" class="Function">∃-syntax</a><a id="5994" class="Symbol">)</a>
<a id="5996" class="Keyword">open</a> <a id="6001" class="Keyword">import</a> <a id="6008" href="Function.html" class="Module">Function</a>     <a id="6021" class="Keyword">using</a> <a id="6027" class="Symbol">(</a><a id="6028" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="6031" class="Symbol">;</a> <a id="6033" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="6036" class="Symbol">;</a> <a id="6038" href="Function.Base.html#615" class="Function">id</a><a id="6040" class="Symbol">;</a> <a id="6042" href="Function.Base.html#636" class="Function">const</a><a id="6047" class="Symbol">)</a>
<a id="6049" class="Keyword">open</a> <a id="6054" class="Keyword">import</a> <a id="6061" href="Level.html" class="Module">Level</a>        <a id="6074" class="Keyword">using</a> <a id="6080" class="Symbol">(</a><a id="6081" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="6086" class="Symbol">;</a> <a id="6088" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="6091" class="Symbol">)</a>

<a id="6094" class="Keyword">import</a> <a id="6101" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="6139" class="Symbol">as</a> <a id="6142" class="Module">Eq</a>
<a id="6145" class="Keyword">open</a> <a id="6150" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="6153" class="Keyword">using</a> <a id="6159" class="Symbol">(</a><a id="6160" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="6163" class="Symbol">;</a> <a id="6165" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="6169" class="Symbol">;</a> <a id="6171" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="6176" class="Symbol">;</a> <a id="6178" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="6181" class="Symbol">;</a> <a id="6183" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="6187" class="Symbol">;</a> <a id="6189" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="6194" class="Symbol">;</a> <a id="6196" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="6204" class="Symbol">;</a> <a id="6206" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="6211" class="Symbol">;</a> <a id="6213" href="Relation.Binary.PropositionalEquality.Core.html#840" class="Function Operator">_≢_</a><a id="6216" class="Symbol">)</a>
<a id="6218" class="Keyword">open</a> <a id="6223" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a>                   <a id="6256" class="Keyword">using</a> <a id="6262" class="Symbol">(</a><a id="6263" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="6269" class="Symbol">;</a> <a id="6271" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="6276" class="Symbol">;</a> <a id="6278" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="6284" class="Symbol">;</a> <a id="6286" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="6288" class="Symbol">)</a>
<a id="6290" class="Keyword">open</a> <a id="6295" class="Keyword">import</a> <a id="6302" href="Relation.Nullary.html" class="Module">Relation.Nullary</a>          <a id="6328" class="Keyword">using</a> <a id="6334" class="Symbol">(</a><a id="6335" href="Relation.Nullary.html#653" class="Function Operator">¬_</a><a id="6337" class="Symbol">)</a>
<a id="6339" class="Keyword">open</a> <a id="6344" class="Keyword">import</a> <a id="6351" href="Relation.Nullary.Negation.html" class="Module">Relation.Nullary.Negation</a> <a id="6377" class="Keyword">using</a> <a id="6383" class="Symbol">(</a><a id="6384" href="Relation.Nullary.Negation.html#929" class="Function">contraposition</a><a id="6398" class="Symbol">)</a>

<a id="6401" class="Keyword">variable</a>
  <a id="6412" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a> <a id="6415" href="simple_essence.html#6415" class="Generalizable">ℓ₂</a> <a id="6418" href="simple_essence.html#6418" class="Generalizable">ℓ₃</a> <a id="6421" class="Symbol">:</a> <a id="6423" href="Agda.Primitive.html#423" class="Postulate">Level</a>
  
<a id="6432" class="Keyword">postulate</a>
  <a id="extensionality"></a><a id="6444" href="simple_essence.html#6444" class="Postulate">extensionality</a> <a id="6459" class="Symbol">:</a> <a id="6461" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="6476" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a> <a id="6479" href="simple_essence.html#6415" class="Generalizable">ℓ₂</a>

</pre>
### Type Classes

Here, we define the abstract type classes we'll be using in our proofs.
We use a slight variation on the approach taken in the standard library "bundles", because it yields cleaner, more succinct, abstract code capable of _automatic instance selection_.

**Note:** We've removed our previously defined custom typeclass: `Additive`, in favor of `Ring` defined in the Agda standard library.
We've kept `Scalable`, for now, in order to get some incremental progress working and checked in before attempting to use `Module` and friends.

<pre class="Agda"><a id="7048" class="Keyword">record</a> <a id="Scalable"></a><a id="7055" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="7064" class="Symbol">(</a><a id="7065" href="simple_essence.html#7065" class="Bound">T</a> <a id="7067" class="Symbol">:</a> <a id="7069" class="PrimitiveType">Set</a> <a id="7073" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="7075" class="Symbol">)</a> <a id="7077" class="Symbol">(</a><a id="7078" href="simple_essence.html#7078" class="Bound">A</a> <a id="7080" class="Symbol">:</a> <a id="7082" class="PrimitiveType">Set</a> <a id="7086" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="7088" class="Symbol">)</a> <a id="7090" class="Symbol">:</a> <a id="7092" class="PrimitiveType">Set</a> <a id="7096" class="Symbol">(</a><a id="7097" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="7107" href="simple_essence.html#7073" class="Bound">ℓ₁</a><a id="7109" class="Symbol">)</a> <a id="7111" class="Keyword">where</a>
  <a id="7119" class="Keyword">infix</a> <a id="7125" class="Number">7</a> <a id="7127" href="simple_essence.html#7143" class="Field Operator">_·_</a>
  <a id="7133" class="Keyword">field</a>
    <a id="Scalable._·_"></a><a id="7143" href="simple_essence.html#7143" class="Field Operator">_·_</a> <a id="7147" class="Symbol">:</a> <a id="7149" href="simple_essence.html#7078" class="Bound">A</a> <a id="7151" class="Symbol">→</a> <a id="7153" href="simple_essence.html#7065" class="Bound">T</a> <a id="7155" class="Symbol">→</a> <a id="7157" href="simple_essence.html#7065" class="Bound">T</a>
<a id="7159" class="Keyword">open</a> <a id="7164" href="simple_essence.html#7055" class="Module">Scalable</a> <a id="7173" class="Symbol">⦃</a> <a id="7175" class="Symbol">...</a> <a id="7179" class="Symbol">⦄</a> <a id="7181" class="Keyword">public</a>

<a id="7189" class="Keyword">record</a> <a id="Ring"></a><a id="7196" href="simple_essence.html#7196" class="Record">Ring</a> <a id="7201" class="Symbol">(</a><a id="7202" href="simple_essence.html#7202" class="Bound">A</a> <a id="7204" class="Symbol">:</a> <a id="7206" class="PrimitiveType">Set</a> <a id="7210" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="7212" class="Symbol">)</a> <a id="7214" class="Symbol">:</a> <a id="7216" class="PrimitiveType">Set</a> <a id="7220" class="Symbol">(</a><a id="7221" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="7231" href="simple_essence.html#7210" class="Bound">ℓ₁</a><a id="7233" class="Symbol">)</a> <a id="7235" class="Keyword">where</a>
  <a id="7243" class="Keyword">infixl</a> <a id="7250" class="Number">6</a> <a id="7252" href="simple_essence.html#7297" class="Field Operator">_+_</a>
  <a id="7258" class="Keyword">infixl</a> <a id="7265" class="Number">7</a> <a id="7267" href="simple_essence.html#7317" class="Field Operator">_*_</a>
  <a id="7273" class="Keyword">infix</a>  <a id="7280" class="Number">8</a> <a id="7282" href="simple_essence.html#7337" class="Field Operator">-_</a>
  <a id="7287" class="Keyword">field</a>
    <a id="Ring._+_"></a><a id="7297" href="simple_essence.html#7297" class="Field Operator">_+_</a> <a id="7301" class="Symbol">:</a> <a id="7303" href="simple_essence.html#7202" class="Bound">A</a> <a id="7305" class="Symbol">→</a> <a id="7307" href="simple_essence.html#7202" class="Bound">A</a> <a id="7309" class="Symbol">→</a> <a id="7311" href="simple_essence.html#7202" class="Bound">A</a>
    <a id="Ring._*_"></a><a id="7317" href="simple_essence.html#7317" class="Field Operator">_*_</a> <a id="7321" class="Symbol">:</a> <a id="7323" href="simple_essence.html#7202" class="Bound">A</a> <a id="7325" class="Symbol">→</a> <a id="7327" href="simple_essence.html#7202" class="Bound">A</a> <a id="7329" class="Symbol">→</a> <a id="7331" href="simple_essence.html#7202" class="Bound">A</a>
    <a id="Ring.-_"></a><a id="7337" href="simple_essence.html#7337" class="Field Operator">-_</a>  <a id="7341" class="Symbol">:</a> <a id="7343" href="simple_essence.html#7202" class="Bound">A</a> <a id="7345" class="Symbol">→</a> <a id="7347" href="simple_essence.html#7202" class="Bound">A</a>
    <a id="Ring.𝟘"></a><a id="7353" href="simple_essence.html#7353" class="Field">𝟘</a>   <a id="7357" class="Symbol">:</a> <a id="7359" href="simple_essence.html#7202" class="Bound">A</a>
    <a id="Ring.𝟙"></a><a id="7365" href="simple_essence.html#7365" class="Field">𝟙</a>   <a id="7369" class="Symbol">:</a> <a id="7371" href="simple_essence.html#7202" class="Bound">A</a>
    <a id="7377" class="Symbol">⦃</a> <a id="Ring.isRing"></a><a id="7379" href="simple_essence.html#7379" class="Field">isRing</a> <a id="7386" class="Symbol">⦄</a> <a id="7388" class="Symbol">:</a> <a id="7390" href="Algebra.Structures.html#12130" class="Record">IsRing</a> <a id="7397" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a> <a id="7401" href="simple_essence.html#7297" class="Field Operator">_+_</a> <a id="7405" href="simple_essence.html#7317" class="Field Operator">_*_</a> <a id="7409" href="simple_essence.html#7337" class="Field Operator">-_</a> <a id="7412" href="simple_essence.html#7353" class="Field">𝟘</a> <a id="7414" href="simple_essence.html#7365" class="Field">𝟙</a>
  <a id="7418" class="Keyword">open</a> <a id="7423" href="Algebra.Structures.html#12130" class="Module">IsRing</a> <a id="7430" href="simple_essence.html#7379" class="Field">isRing</a> <a id="7437" class="Keyword">public</a>
  <a id="7446" class="Keyword">instance</a>
    <a id="Ring.scalableRing"></a><a id="7459" href="simple_essence.html#7459" class="Function">scalableRing</a> <a id="7472" class="Symbol">:</a> <a id="7474" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="7483" href="simple_essence.html#7202" class="Bound">A</a> <a id="7485" href="simple_essence.html#7202" class="Bound">A</a>
    <a id="7491" href="simple_essence.html#7459" class="Function">scalableRing</a> <a id="7504" class="Symbol">=</a> <a id="7506" class="Keyword">record</a>
      <a id="7519" class="Symbol">{</a> <a id="7521" href="simple_essence.html#7143" class="Field Operator">_·_</a> <a id="7525" class="Symbol">=</a> <a id="7527" href="simple_essence.html#7317" class="Field Operator">_*_</a>
      <a id="7537" class="Symbol">}</a>
  <a id="7541" class="Keyword">open</a> <a id="7546" href="simple_essence.html#7055" class="Module">Scalable</a> <a id="7555" href="simple_essence.html#7459" class="Function">scalableRing</a>
<a id="7568" class="Keyword">open</a> <a id="7573" href="simple_essence.html#7196" class="Module">Ring</a> <a id="7578" class="Symbol">⦃</a> <a id="7580" class="Symbol">...</a> <a id="7584" class="Symbol">⦄</a> <a id="7586" class="Keyword">public</a>
    
</pre>
### Linear Maps

Here, we capture our intended meaning of _linearity_.

We take the vector-centric definition offered by Conal in his paper:

> A linear map is one that distributes over _vector_ addition and _scalar_ multiplication.

<pre class="Agda"><a id="7845" class="Keyword">record</a> <a id="LinMap"></a><a id="7852" href="simple_essence.html#7852" class="Record">LinMap</a> <a id="7859" class="Symbol">(</a><a id="7860" href="simple_essence.html#7860" class="Bound">A</a> <a id="7862" class="Symbol">:</a> <a id="7864" class="PrimitiveType">Set</a> <a id="7868" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="7870" class="Symbol">)</a> <a id="7872" class="Symbol">(</a><a id="7873" href="simple_essence.html#7873" class="Bound">B</a> <a id="7875" class="Symbol">:</a> <a id="7877" class="PrimitiveType">Set</a> <a id="7881" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="7883" class="Symbol">)</a> <a id="7885" class="Symbol">{</a><a id="7886" href="simple_essence.html#7886" class="Bound">§</a> <a id="7888" class="Symbol">:</a> <a id="7890" class="PrimitiveType">Set</a> <a id="7894" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="7896" class="Symbol">}</a>
              <a id="7912" class="Symbol">⦃</a> <a id="7914" href="simple_essence.html#7914" class="Bound">_</a> <a id="7916" class="Symbol">:</a> <a id="7918" href="simple_essence.html#7196" class="Record">Ring</a> <a id="7923" href="simple_essence.html#7860" class="Bound">A</a> <a id="7925" class="Symbol">⦄</a> <a id="7927" class="Symbol">⦃</a> <a id="7929" href="simple_essence.html#7929" class="Bound">_</a> <a id="7931" class="Symbol">:</a> <a id="7933" href="simple_essence.html#7196" class="Record">Ring</a> <a id="7938" href="simple_essence.html#7873" class="Bound">B</a> <a id="7940" class="Symbol">⦄</a>
              <a id="7956" class="Symbol">⦃</a> <a id="7958" href="simple_essence.html#7958" class="Bound">_</a> <a id="7960" class="Symbol">:</a> <a id="7962" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="7971" href="simple_essence.html#7860" class="Bound">A</a> <a id="7973" href="simple_essence.html#7886" class="Bound">§</a> <a id="7975" class="Symbol">⦄</a>   <a id="7979" class="Symbol">⦃</a> <a id="7981" href="simple_essence.html#7981" class="Bound">_</a> <a id="7983" class="Symbol">:</a> <a id="7985" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="7994" href="simple_essence.html#7873" class="Bound">B</a> <a id="7996" href="simple_essence.html#7886" class="Bound">§</a> <a id="7998" class="Symbol">⦄</a>
              <a id="8014" class="Symbol">:</a> <a id="8016" class="PrimitiveType">Set</a> <a id="8020" href="simple_essence.html#7868" class="Bound">ℓ₁</a> <a id="8023" class="Keyword">where</a>
  <a id="8031" class="Keyword">constructor</a> <a id="mkLM"></a><a id="8043" href="simple_essence.html#8043" class="InductiveConstructor">mkLM</a>
  <a id="8050" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="8060" href="simple_essence.html#8060" class="Field">f</a>      <a id="8067" class="Symbol">:</a> <a id="8069" href="simple_essence.html#7860" class="Bound">A</a> <a id="8071" class="Symbol">→</a> <a id="8073" href="simple_essence.html#7873" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="8080" href="simple_essence.html#8080" class="Field">adds</a>   <a id="8087" class="Symbol">:</a> <a id="8089" class="Symbol">∀</a> <a id="8091" class="Symbol">{</a><a id="8092" href="simple_essence.html#8092" class="Bound">a</a> <a id="8094" href="simple_essence.html#8094" class="Bound">b</a> <a id="8096" class="Symbol">:</a> <a id="8098" href="simple_essence.html#7860" class="Bound">A</a><a id="8099" class="Symbol">}</a>
             <a id="8114" class="Comment">---------------------</a>
          <a id="8146" class="Symbol">→</a> <a id="8148" href="simple_essence.html#8060" class="Field">f</a> <a id="8150" class="Symbol">(</a><a id="8151" href="simple_essence.html#8092" class="Bound">a</a> <a id="8153" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="8155" href="simple_essence.html#8094" class="Bound">b</a><a id="8156" class="Symbol">)</a> <a id="8158" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8160" href="simple_essence.html#8060" class="Field">f</a> <a id="8162" href="simple_essence.html#8092" class="Bound">a</a> <a id="8164" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="8166" href="simple_essence.html#8060" class="Field">f</a> <a id="8168" href="simple_essence.html#8094" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="8175" href="simple_essence.html#8175" class="Field">scales</a> <a id="8182" class="Symbol">:</a> <a id="8184" class="Symbol">∀</a> <a id="8186" class="Symbol">{</a><a id="8187" href="simple_essence.html#8187" class="Bound">s</a> <a id="8189" class="Symbol">:</a> <a id="8191" href="simple_essence.html#7886" class="Bound">§</a><a id="8192" class="Symbol">}</a> <a id="8194" class="Symbol">{</a><a id="8195" href="simple_essence.html#8195" class="Bound">a</a> <a id="8197" class="Symbol">:</a> <a id="8199" href="simple_essence.html#7860" class="Bound">A</a><a id="8200" class="Symbol">}</a>
             <a id="8215" class="Comment">-------------------</a>
          <a id="8245" class="Symbol">→</a> <a id="8247" href="simple_essence.html#8060" class="Field">f</a> <a id="8249" class="Symbol">(</a><a id="8250" href="simple_essence.html#8187" class="Bound">s</a> <a id="8252" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="8254" href="simple_essence.html#8195" class="Bound">a</a><a id="8255" class="Symbol">)</a> <a id="8257" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8259" href="simple_essence.html#8187" class="Bound">s</a> <a id="8261" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="8263" href="simple_essence.html#8060" class="Field">f</a> <a id="8265" href="simple_essence.html#8195" class="Bound">a</a>

<a id="8268" class="Keyword">open</a> <a id="8273" href="simple_essence.html#7852" class="Module">LinMap</a> <a id="8280" class="Symbol">⦃</a> <a id="8282" class="Symbol">...</a> <a id="8286" class="Symbol">⦄</a> <a id="8288" class="Keyword">public</a>

<a id="8296" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="8322" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="8370" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="8382" href="simple_essence.html#8382" class="Postulate">⊸≡</a> <a id="8385" class="Symbol">:</a> <a id="8387" class="Symbol">{</a><a id="8388" href="simple_essence.html#8388" class="Bound">A</a> <a id="8390" class="Symbol">:</a> <a id="8392" class="PrimitiveType">Set</a> <a id="8396" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="8398" class="Symbol">}</a> <a id="8400" class="Symbol">{</a><a id="8401" href="simple_essence.html#8401" class="Bound">B</a> <a id="8403" class="Symbol">:</a> <a id="8405" class="PrimitiveType">Set</a> <a id="8409" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="8411" class="Symbol">}</a> <a id="8413" class="Symbol">{</a><a id="8414" href="simple_essence.html#8414" class="Bound">§</a> <a id="8416" class="Symbol">:</a> <a id="8418" class="PrimitiveType">Set</a> <a id="8422" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="8424" class="Symbol">}</a>
       <a id="8433" class="Symbol">⦃</a> <a id="8435" href="simple_essence.html#8435" class="Bound">_</a> <a id="8437" class="Symbol">:</a> <a id="8439" href="simple_essence.html#7196" class="Record">Ring</a> <a id="8444" href="simple_essence.html#8388" class="Bound">A</a> <a id="8446" class="Symbol">⦄</a> <a id="8448" class="Symbol">⦃</a> <a id="8450" href="simple_essence.html#8450" class="Bound">_</a> <a id="8452" class="Symbol">:</a> <a id="8454" href="simple_essence.html#7196" class="Record">Ring</a> <a id="8459" href="simple_essence.html#8401" class="Bound">B</a> <a id="8461" class="Symbol">⦄</a>
       <a id="8470" class="Symbol">⦃</a> <a id="8472" href="simple_essence.html#8472" class="Bound">_</a> <a id="8474" class="Symbol">:</a> <a id="8476" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="8485" href="simple_essence.html#8388" class="Bound">A</a> <a id="8487" href="simple_essence.html#8414" class="Bound">§</a> <a id="8489" class="Symbol">⦄</a> <a id="8491" class="Symbol">⦃</a> <a id="8493" href="simple_essence.html#8493" class="Bound">_</a> <a id="8495" class="Symbol">:</a> <a id="8497" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="8506" href="simple_essence.html#8401" class="Bound">B</a> <a id="8508" href="simple_essence.html#8414" class="Bound">§</a> <a id="8510" class="Symbol">⦄</a>
       <a id="8519" class="Symbol">{</a><a id="8520" href="simple_essence.html#8520" class="Bound">lm₁</a> <a id="8524" href="simple_essence.html#8524" class="Bound">lm₂</a> <a id="8528" class="Symbol">:</a> <a id="8530" href="simple_essence.html#7852" class="Record">LinMap</a> <a id="8537" href="simple_essence.html#8388" class="Bound">A</a> <a id="8539" href="simple_essence.html#8401" class="Bound">B</a> <a id="8541" class="Symbol">{</a><a id="8542" href="simple_essence.html#8414" class="Bound">§</a><a id="8543" class="Symbol">}}</a>
    <a id="8550" class="Symbol">→</a> <a id="8552" href="simple_essence.html#8060" class="Field">LinMap.f</a> <a id="8561" href="simple_essence.html#8520" class="Bound">lm₁</a> <a id="8565" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8567" href="simple_essence.html#8060" class="Field">LinMap.f</a> <a id="8576" href="simple_essence.html#8524" class="Bound">lm₂</a>
       <a id="8587" class="Comment">--------------------------</a>
    <a id="8618" class="Symbol">→</a> <a id="8620" href="simple_essence.html#8520" class="Bound">lm₁</a> <a id="8624" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8626" href="simple_essence.html#8524" class="Bound">lm₂</a>

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

<pre class="Agda"><a id="9580" class="Keyword">record</a> <a id="VectorSpace"></a><a id="9587" href="simple_essence.html#9587" class="Record">VectorSpace</a>
  <a id="9601" class="Symbol">(</a><a id="9602" href="simple_essence.html#9602" class="Bound">T</a> <a id="9604" class="Symbol">:</a> <a id="9606" class="PrimitiveType">Set</a> <a id="9610" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="9612" class="Symbol">)</a> <a id="9614" class="Symbol">(</a><a id="9615" href="simple_essence.html#9615" class="Bound">A</a> <a id="9617" class="Symbol">:</a> <a id="9619" class="PrimitiveType">Set</a> <a id="9623" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="9625" class="Symbol">)</a>
  <a id="9629" class="Symbol">⦃</a> <a id="9631" href="simple_essence.html#9631" class="Bound">_</a> <a id="9633" class="Symbol">:</a> <a id="9635" href="simple_essence.html#7196" class="Record">Ring</a> <a id="9640" href="simple_essence.html#9602" class="Bound">T</a> <a id="9642" class="Symbol">⦄</a> <a id="9644" class="Symbol">⦃</a> <a id="9646" href="simple_essence.html#9646" class="Bound">_</a> <a id="9648" class="Symbol">:</a> <a id="9650" href="simple_essence.html#7196" class="Record">Ring</a> <a id="9655" href="simple_essence.html#9615" class="Bound">A</a> <a id="9657" class="Symbol">⦄</a> <a id="9659" class="Symbol">⦃</a> <a id="9661" href="simple_essence.html#9661" class="Bound">_</a> <a id="9663" class="Symbol">:</a> <a id="9665" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="9674" href="simple_essence.html#9602" class="Bound">T</a> <a id="9676" href="simple_essence.html#9615" class="Bound">A</a> <a id="9678" class="Symbol">⦄</a>
  <a id="9682" class="Symbol">:</a> <a id="9684" class="PrimitiveType">Set</a> <a id="9688" class="Symbol">(</a><a id="9689" href="Agda.Primitive.html#606" class="Primitive">Level.suc</a> <a id="9699" href="simple_essence.html#9610" class="Bound">ℓ₁</a><a id="9701" class="Symbol">)</a> <a id="9703" class="Keyword">where</a>
  <a id="9711" class="Keyword">infix</a>  <a id="9718" class="Number">7</a> <a id="9720" href="simple_essence.html#9802" class="Field Operator">_⊙_</a>
  <a id="9726" class="Keyword">field</a>
    <a id="VectorSpace.I"></a><a id="9736" href="simple_essence.html#9736" class="Field">I</a>     <a id="9742" class="Symbol">:</a> <a id="9744" class="PrimitiveType">Set</a> <a id="9748" href="simple_essence.html#9610" class="Bound">ℓ₁</a>
    <a id="VectorSpace.index"></a><a id="9755" href="simple_essence.html#9755" class="Field">index</a> <a id="9761" class="Symbol">:</a> <a id="9763" href="simple_essence.html#9736" class="Field">I</a> <a id="9765" class="Symbol">→</a> <a id="9767" href="simple_essence.html#9602" class="Bound">T</a> <a id="9769" class="Symbol">→</a> <a id="9771" href="simple_essence.html#9615" class="Bound">A</a>
    <a id="VectorSpace.basisSet"></a><a id="9777" href="simple_essence.html#9777" class="Field">basisSet</a>    <a id="9789" class="Symbol">:</a> <a id="9791" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="9796" href="simple_essence.html#9602" class="Bound">T</a>
    <a id="VectorSpace._⊙_"></a><a id="9802" href="simple_essence.html#9802" class="Field Operator">_⊙_</a>         <a id="9814" class="Symbol">:</a> <a id="9816" href="simple_essence.html#9602" class="Bound">T</a> <a id="9818" class="Symbol">→</a> <a id="9820" href="simple_essence.html#9602" class="Bound">T</a> <a id="9822" class="Symbol">→</a> <a id="9824" href="simple_essence.html#9615" class="Bound">A</a>
    <a id="9830" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.⊙-distrib-+"></a><a id="9880" href="simple_essence.html#9880" class="Field">⊙-distrib-+</a> <a id="9892" class="Symbol">:</a> <a id="9894" class="Symbol">∀</a> <a id="9896" class="Symbol">{</a><a id="9897" href="simple_essence.html#9897" class="Bound">a</a> <a id="9899" href="simple_essence.html#9899" class="Bound">b</a> <a id="9901" href="simple_essence.html#9901" class="Bound">c</a> <a id="9903" class="Symbol">:</a> <a id="9905" href="simple_essence.html#9602" class="Bound">T</a><a id="9906" class="Symbol">}</a>
                  <a id="9926" class="Comment">-------------------------------</a>
               <a id="9973" class="Symbol">→</a> <a id="9975" href="simple_essence.html#9897" class="Bound">a</a> <a id="9977" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="9979" class="Symbol">(</a><a id="9980" href="simple_essence.html#9899" class="Bound">b</a> <a id="9982" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="9984" href="simple_essence.html#9901" class="Bound">c</a><a id="9985" class="Symbol">)</a> <a id="9987" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9989" class="Symbol">(</a><a id="9990" href="simple_essence.html#9897" class="Bound">a</a> <a id="9992" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="9994" href="simple_essence.html#9899" class="Bound">b</a><a id="9995" class="Symbol">)</a> <a id="9997" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="9999" class="Symbol">(</a><a id="10000" href="simple_essence.html#9897" class="Bound">a</a> <a id="10002" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="10004" href="simple_essence.html#9901" class="Bound">c</a><a id="10005" class="Symbol">)</a>
    <a id="VectorSpace.⊙-comm-·"></a><a id="10011" href="simple_essence.html#10011" class="Field">⊙-comm-·</a>    <a id="10023" class="Symbol">:</a> <a id="10025" class="Symbol">∀</a> <a id="10027" class="Symbol">{</a><a id="10028" href="simple_essence.html#10028" class="Bound">s</a> <a id="10030" class="Symbol">:</a> <a id="10032" href="simple_essence.html#9615" class="Bound">A</a><a id="10033" class="Symbol">}</a> <a id="10035" class="Symbol">{</a><a id="10036" href="simple_essence.html#10036" class="Bound">a</a> <a id="10038" href="simple_essence.html#10038" class="Bound">b</a> <a id="10040" class="Symbol">:</a> <a id="10042" href="simple_essence.html#9602" class="Bound">T</a><a id="10043" class="Symbol">}</a>
                  <a id="10063" class="Comment">-------------------------</a>
               <a id="10104" class="Symbol">→</a> <a id="10106" href="simple_essence.html#10036" class="Bound">a</a> <a id="10108" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="10110" class="Symbol">(</a><a id="10111" href="simple_essence.html#10028" class="Bound">s</a> <a id="10113" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="10115" href="simple_essence.html#10038" class="Bound">b</a><a id="10116" class="Symbol">)</a> <a id="10118" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10120" href="simple_essence.html#10028" class="Bound">s</a> <a id="10122" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="10124" class="Symbol">(</a><a id="10125" href="simple_essence.html#10036" class="Bound">a</a> <a id="10127" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="10129" href="simple_essence.html#10038" class="Bound">b</a><a id="10130" class="Symbol">)</a>
    <a id="VectorSpace.orthonormal"></a><a id="10136" href="simple_essence.html#10136" class="Field">orthonormal</a> <a id="10148" class="Symbol">:</a> <a id="10150" class="Symbol">∀</a> <a id="10152" class="Symbol">{</a><a id="10153" href="simple_essence.html#10153" class="Bound">f</a> <a id="10155" class="Symbol">:</a> <a id="10157" href="simple_essence.html#9602" class="Bound">T</a> <a id="10159" class="Symbol">→</a> <a id="10161" href="simple_essence.html#9615" class="Bound">A</a><a id="10162" class="Symbol">}</a>
               <a id="10179" class="Symbol">→</a> <a id="10181" class="Symbol">{</a><a id="10182" href="simple_essence.html#10182" class="Bound">x</a> <a id="10184" class="Symbol">:</a> <a id="10186" href="simple_essence.html#9602" class="Bound">T</a><a id="10187" class="Symbol">}</a>
                  <a id="10207" class="Comment">------------------------------------</a>
               <a id="10259" class="Symbol">→</a> <a id="10261" class="Symbol">(</a> <a id="10263" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10269" class="Symbol">(λ</a> <a id="10272" href="simple_essence.html#10272" class="Bound">acc</a> <a id="10276" href="simple_essence.html#10276" class="Bound">v</a> <a id="10278" class="Symbol">→</a> <a id="10280" href="simple_essence.html#10272" class="Bound">acc</a> <a id="10284" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="10286" class="Symbol">(</a><a id="10287" href="simple_essence.html#10153" class="Bound">f</a> <a id="10289" href="simple_essence.html#10276" class="Bound">v</a><a id="10290" class="Symbol">)</a> <a id="10292" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="10294" href="simple_essence.html#10276" class="Bound">v</a><a id="10295" class="Symbol">)</a>
                          <a id="10323" href="simple_essence.html#7353" class="Field">𝟘</a> <a id="10325" href="simple_essence.html#9777" class="Field">basisSet</a>
                  <a id="10352" class="Symbol">)</a> <a id="10354" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="10356" href="simple_essence.html#10182" class="Bound">x</a> <a id="10358" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="10360" href="simple_essence.html#10153" class="Bound">f</a> <a id="10362" href="simple_essence.html#10182" class="Bound">x</a>
<a id="10364" class="Keyword">open</a> <a id="10369" href="simple_essence.html#9587" class="Module">VectorSpace</a> <a id="10381" class="Symbol">⦃</a> <a id="10383" class="Symbol">...</a> <a id="10387" class="Symbol">⦄</a> <a id="10389" class="Keyword">public</a>

</pre>
### Isomorphism 1: `(A ⊸ s) ↔ A`

Here, I prove that a linear map from some "vector" type `T` to a scalar of its _carrier_ type `A` is isomorphic to `T`.

<pre class="Agda"><a id="a⊸§→a"></a><a id="10565" href="simple_essence.html#10565" class="Function">a⊸§→a</a> <a id="10571" class="Symbol">:</a> <a id="10573" class="Symbol">{</a><a id="10574" href="simple_essence.html#10574" class="Bound">T</a> <a id="10576" class="Symbol">:</a> <a id="10578" class="PrimitiveType">Set</a> <a id="10582" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="10584" class="Symbol">}</a> <a id="10586" class="Symbol">{</a><a id="10587" href="simple_essence.html#10587" class="Bound">A</a> <a id="10589" class="Symbol">:</a> <a id="10591" class="PrimitiveType">Set</a> <a id="10595" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="10597" class="Symbol">}</a>
         <a id="10608" class="Symbol">⦃</a> <a id="10610" href="simple_essence.html#10610" class="Bound">_</a> <a id="10612" class="Symbol">:</a> <a id="10614" href="simple_essence.html#7196" class="Record">Ring</a> <a id="10619" href="simple_essence.html#10574" class="Bound">T</a> <a id="10621" class="Symbol">⦄</a> <a id="10623" class="Symbol">⦃</a> <a id="10625" href="simple_essence.html#10625" class="Bound">_</a> <a id="10627" class="Symbol">:</a> <a id="10629" href="simple_essence.html#7196" class="Record">Ring</a> <a id="10634" href="simple_essence.html#10587" class="Bound">A</a> <a id="10636" class="Symbol">⦄</a>
         <a id="10647" class="Symbol">⦃</a> <a id="10649" href="simple_essence.html#10649" class="Bound">_</a> <a id="10651" class="Symbol">:</a> <a id="10653" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="10662" href="simple_essence.html#10574" class="Bound">T</a> <a id="10664" href="simple_essence.html#10587" class="Bound">A</a> <a id="10666" class="Symbol">⦄</a>
         <a id="10677" class="Symbol">⦃</a> <a id="10679" href="simple_essence.html#10679" class="Bound">_</a> <a id="10681" class="Symbol">:</a> <a id="10683" href="simple_essence.html#9587" class="Record">VectorSpace</a> <a id="10695" href="simple_essence.html#10574" class="Bound">T</a> <a id="10697" href="simple_essence.html#10587" class="Bound">A</a> <a id="10699" class="Symbol">⦄</a>
         <a id="10710" class="Comment">------------------------------</a>
      <a id="10747" class="Symbol">→</a> <a id="10749" href="simple_essence.html#7852" class="Record">LinMap</a> <a id="10756" href="simple_essence.html#10574" class="Bound">T</a> <a id="10758" href="simple_essence.html#10587" class="Bound">A</a> <a id="10760" class="Symbol">{</a><a id="10761" href="simple_essence.html#10587" class="Bound">A</a><a id="10762" class="Symbol">}</a> <a id="10764" class="Symbol">→</a> <a id="10766" href="simple_essence.html#10574" class="Bound">T</a>
<a id="10768" href="simple_essence.html#10565" class="Function">a⊸§→a</a> <a id="10774" class="Symbol">=</a> <a id="10776" class="Symbol">λ</a> <a id="10778" class="Symbol">{</a> <a id="10780" href="simple_essence.html#10780" class="Bound">lm</a> <a id="10783" class="Symbol">→</a> <a id="10785" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10791" class="Symbol">(λ</a> <a id="10794" href="simple_essence.html#10794" class="Bound">acc</a> <a id="10798" href="simple_essence.html#10798" class="Bound">v</a> <a id="10800" class="Symbol">→</a>
                     <a id="10823" href="simple_essence.html#10794" class="Bound">acc</a> <a id="10827" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="10829" class="Symbol">(</a><a id="10830" href="simple_essence.html#8060" class="Field">LinMap.f</a> <a id="10839" href="simple_essence.html#10780" class="Bound">lm</a> <a id="10842" href="simple_essence.html#10798" class="Bound">v</a><a id="10843" class="Symbol">)</a> <a id="10845" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="10847" href="simple_essence.html#10798" class="Bound">v</a><a id="10848" class="Symbol">)</a> <a id="10850" href="simple_essence.html#7353" class="Field">𝟘</a> <a id="10852" href="simple_essence.html#9777" class="Field">basisSet</a> <a id="10861" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="10864" href="simple_essence.html#10864" class="Function">a⊸§←a</a> <a id="10870" class="Symbol">:</a> <a id="10872" class="Symbol">{</a><a id="10873" href="simple_essence.html#10873" class="Bound">T</a> <a id="10875" class="Symbol">:</a> <a id="10877" class="PrimitiveType">Set</a> <a id="10881" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="10883" class="Symbol">}</a> <a id="10885" class="Symbol">{</a><a id="10886" href="simple_essence.html#10886" class="Bound">A</a> <a id="10888" class="Symbol">:</a> <a id="10890" class="PrimitiveType">Set</a> <a id="10894" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="10896" class="Symbol">}</a>
         <a id="10907" class="Symbol">⦃</a> <a id="10909" href="simple_essence.html#10909" class="Bound">_</a> <a id="10911" class="Symbol">:</a> <a id="10913" href="simple_essence.html#7196" class="Record">Ring</a> <a id="10918" href="simple_essence.html#10873" class="Bound">T</a> <a id="10920" class="Symbol">⦄</a> <a id="10922" class="Symbol">⦃</a> <a id="10924" href="simple_essence.html#10924" class="Bound">_</a> <a id="10926" class="Symbol">:</a> <a id="10928" href="simple_essence.html#7196" class="Record">Ring</a> <a id="10933" href="simple_essence.html#10886" class="Bound">A</a> <a id="10935" class="Symbol">⦄</a>
         <a id="10946" class="Symbol">⦃</a> <a id="10948" href="simple_essence.html#10948" class="Bound">_</a> <a id="10950" class="Symbol">:</a> <a id="10952" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="10961" href="simple_essence.html#10873" class="Bound">T</a> <a id="10963" href="simple_essence.html#10886" class="Bound">A</a> <a id="10965" class="Symbol">⦄</a>
         <a id="10976" class="Symbol">⦃</a> <a id="10978" href="simple_essence.html#10978" class="Bound">_</a> <a id="10980" class="Symbol">:</a> <a id="10982" href="simple_essence.html#9587" class="Record">VectorSpace</a> <a id="10994" href="simple_essence.html#10873" class="Bound">T</a> <a id="10996" href="simple_essence.html#10886" class="Bound">A</a> <a id="10998" class="Symbol">⦄</a>
         <a id="11009" class="Comment">--------------------------------------</a>
      <a id="11054" class="Symbol">→</a> <a id="11056" href="simple_essence.html#10873" class="Bound">T</a> <a id="11058" class="Symbol">→</a> <a id="11060" href="simple_essence.html#7852" class="Record">LinMap</a> <a id="11067" href="simple_essence.html#10873" class="Bound">T</a> <a id="11069" href="simple_essence.html#10886" class="Bound">A</a> <a id="11071" class="Symbol">{</a><a id="11072" href="simple_essence.html#10886" class="Bound">A</a><a id="11073" class="Symbol">}</a>
<a id="11075" href="simple_essence.html#10864" class="Function">a⊸§←a</a> <a id="11081" class="Symbol">=</a> <a id="11083" class="Symbol">λ</a> <a id="11085" class="Symbol">{</a> <a id="11087" href="simple_essence.html#11087" class="Bound">a</a> <a id="11089" class="Symbol">→</a> <a id="11091" href="simple_essence.html#8043" class="InductiveConstructor">mkLM</a> <a id="11096" class="Symbol">(</a><a id="11097" href="simple_essence.html#11087" class="Bound">a</a> <a id="11099" href="simple_essence.html#9802" class="Field Operator">⊙_</a><a id="11101" class="Symbol">)</a> <a id="11103" href="simple_essence.html#9880" class="Field">⊙-distrib-+</a> <a id="11115" href="simple_essence.html#10011" class="Field">⊙-comm-·</a> <a id="11124" class="Symbol">}</a>

<a id="11127" class="Comment">-- Danger, Will Robinson!</a>
<a id="11153" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="11165" href="simple_essence.html#11165" class="Postulate">x·z≡y·z→x≡y</a> <a id="11177" class="Symbol">:</a> <a id="11179" class="Symbol">{</a><a id="11180" href="simple_essence.html#11180" class="Bound">T</a> <a id="11182" class="Symbol">:</a> <a id="11184" class="PrimitiveType">Set</a> <a id="11188" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="11190" class="Symbol">}</a> <a id="11192" class="Symbol">{</a><a id="11193" href="simple_essence.html#11193" class="Bound">A</a> <a id="11195" class="Symbol">:</a> <a id="11197" class="PrimitiveType">Set</a> <a id="11201" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="11203" class="Symbol">}</a>
                 <a id="11222" class="Symbol">⦃</a> <a id="11224" href="simple_essence.html#11224" class="Bound">_</a> <a id="11226" class="Symbol">:</a> <a id="11228" href="simple_essence.html#7196" class="Record">Ring</a> <a id="11233" href="simple_essence.html#11180" class="Bound">T</a> <a id="11235" class="Symbol">⦄</a> <a id="11237" class="Symbol">⦃</a> <a id="11239" href="simple_essence.html#11239" class="Bound">_</a> <a id="11241" class="Symbol">:</a> <a id="11243" href="simple_essence.html#7196" class="Record">Ring</a> <a id="11248" href="simple_essence.html#11193" class="Bound">A</a> <a id="11250" class="Symbol">⦄</a>
                 <a id="11269" class="Symbol">⦃</a> <a id="11271" href="simple_essence.html#11271" class="Bound">_</a> <a id="11273" class="Symbol">:</a> <a id="11275" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="11284" href="simple_essence.html#11180" class="Bound">T</a> <a id="11286" href="simple_essence.html#11193" class="Bound">A</a> <a id="11288" class="Symbol">⦄</a> <a id="11290" class="Symbol">⦃</a> <a id="11292" href="simple_essence.html#11292" class="Bound">_</a> <a id="11294" class="Symbol">:</a> <a id="11296" href="simple_essence.html#9587" class="Record">VectorSpace</a> <a id="11308" href="simple_essence.html#11180" class="Bound">T</a> <a id="11310" href="simple_essence.html#11193" class="Bound">A</a> <a id="11312" class="Symbol">⦄</a>
                 <a id="11331" class="Symbol">{</a><a id="11332" href="simple_essence.html#11332" class="Bound">x</a> <a id="11334" href="simple_essence.html#11334" class="Bound">y</a> <a id="11336" class="Symbol">:</a> <a id="11338" href="simple_essence.html#11180" class="Bound">T</a><a id="11339" class="Symbol">}</a>
              <a id="11355" class="Symbol">→</a> <a id="11357" class="Symbol">(∀</a> <a id="11360" class="Symbol">{</a><a id="11361" href="simple_essence.html#11361" class="Bound">z</a> <a id="11363" class="Symbol">:</a> <a id="11365" href="simple_essence.html#11180" class="Bound">T</a><a id="11366" class="Symbol">}</a> <a id="11368" class="Symbol">→</a> <a id="11370" href="simple_essence.html#11332" class="Bound">x</a> <a id="11372" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="11374" href="simple_essence.html#11361" class="Bound">z</a> <a id="11376" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11378" href="simple_essence.html#11334" class="Bound">y</a> <a id="11380" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="11382" href="simple_essence.html#11361" class="Bound">z</a><a id="11383" class="Symbol">)</a>
                 <a id="11402" class="Comment">---------------------------------------------</a>
              <a id="11462" class="Symbol">→</a> <a id="11464" href="simple_essence.html#11332" class="Bound">x</a> <a id="11466" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="11468" href="simple_essence.html#11334" class="Bound">y</a>
<a id="11470" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="11530" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="11597" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="11628" href="simple_essence.html#11628" class="Function">a⊸§↔a</a> <a id="11634" class="Symbol">:</a> <a id="11636" class="Symbol">{</a><a id="11637" href="simple_essence.html#11637" class="Bound">T</a> <a id="11639" class="Symbol">:</a> <a id="11641" class="PrimitiveType">Set</a> <a id="11645" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="11647" class="Symbol">}</a> <a id="11649" class="Symbol">{</a><a id="11650" href="simple_essence.html#11650" class="Bound">A</a> <a id="11652" class="Symbol">:</a> <a id="11654" class="PrimitiveType">Set</a> <a id="11658" href="simple_essence.html#6412" class="Generalizable">ℓ₁</a><a id="11660" class="Symbol">}</a>
         <a id="11671" class="Symbol">⦃</a> <a id="11673" href="simple_essence.html#11673" class="Bound">_</a> <a id="11675" class="Symbol">:</a> <a id="11677" href="simple_essence.html#7196" class="Record">Ring</a> <a id="11682" href="simple_essence.html#11637" class="Bound">T</a> <a id="11684" class="Symbol">⦄</a> <a id="11686" class="Symbol">⦃</a> <a id="11688" href="simple_essence.html#11688" class="Bound">_</a> <a id="11690" class="Symbol">:</a> <a id="11692" href="simple_essence.html#7196" class="Record">Ring</a> <a id="11697" href="simple_essence.html#11650" class="Bound">A</a> <a id="11699" class="Symbol">⦄</a>
         <a id="11710" class="Symbol">⦃</a> <a id="11712" href="simple_essence.html#11712" class="Bound">_</a> <a id="11714" class="Symbol">:</a> <a id="11716" href="simple_essence.html#7055" class="Record">Scalable</a> <a id="11725" href="simple_essence.html#11637" class="Bound">T</a> <a id="11727" href="simple_essence.html#11650" class="Bound">A</a> <a id="11729" class="Symbol">⦄</a> <a id="11731" class="Symbol">⦃</a> <a id="11733" href="simple_essence.html#11733" class="Bound">_</a> <a id="11735" class="Symbol">:</a> <a id="11737" href="simple_essence.html#9587" class="Record">VectorSpace</a> <a id="11749" href="simple_essence.html#11637" class="Bound">T</a> <a id="11751" href="simple_essence.html#11650" class="Bound">A</a> <a id="11753" class="Symbol">⦄</a>
         <a id="11764" class="Comment">---------------------------------------------</a>
      <a id="11816" class="Symbol">→</a> <a id="11818" class="Symbol">(</a><a id="11819" href="simple_essence.html#7852" class="Record">LinMap</a> <a id="11826" href="simple_essence.html#11637" class="Bound">T</a> <a id="11828" href="simple_essence.html#11650" class="Bound">A</a><a id="11829" class="Symbol">)</a> <a id="11831" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="11833" href="simple_essence.html#11637" class="Bound">T</a>
<a id="11835" href="simple_essence.html#11628" class="Function">a⊸§↔a</a> <a id="11841" class="Symbol">=</a>
  <a id="11845" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="11849" class="Symbol">{</a><a id="11850" class="Argument">f</a> <a id="11852" class="Symbol">=</a> <a id="11854" href="simple_essence.html#10565" class="Function">a⊸§→a</a><a id="11859" class="Symbol">}</a> <a id="11861" class="Symbol">{</a><a id="11862" class="Argument">f⁻¹</a> <a id="11866" class="Symbol">=</a> <a id="11868" href="simple_essence.html#10864" class="Function">a⊸§←a</a><a id="11873" class="Symbol">}</a>
      <a id="11881" class="Symbol">(</a> <a id="11883" class="Symbol">(λ</a> <a id="11886" class="Symbol">{</a><a id="11887" href="simple_essence.html#11887" class="Bound">x</a> <a id="11889" class="Symbol">→</a> <a id="11891" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="11915" href="simple_essence.html#10565" class="Function">a⊸§→a</a> <a id="11921" class="Symbol">(</a><a id="11922" href="simple_essence.html#10864" class="Function">a⊸§←a</a> <a id="11928" href="simple_essence.html#11887" class="Bound">x</a><a id="11929" class="Symbol">)</a>
                <a id="11947" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="11969" href="simple_essence.html#10565" class="Function">a⊸§→a</a> <a id="11975" class="Symbol">(</a><a id="11976" href="simple_essence.html#8043" class="InductiveConstructor">mkLM</a> <a id="11981" class="Symbol">(</a><a id="11982" href="simple_essence.html#11887" class="Bound">x</a> <a id="11984" href="simple_essence.html#9802" class="Field Operator">⊙_</a><a id="11986" class="Symbol">)</a> <a id="11988" href="simple_essence.html#9880" class="Field">⊙-distrib-+</a> <a id="12000" href="simple_essence.html#10011" class="Field">⊙-comm-·</a><a id="12008" class="Symbol">)</a>
                <a id="12026" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="12048" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12054" class="Symbol">(λ</a> <a id="12057" href="simple_essence.html#12057" class="Bound">acc</a> <a id="12061" href="simple_essence.html#12061" class="Bound">v</a> <a id="12063" class="Symbol">→</a> <a id="12065" href="simple_essence.html#12057" class="Bound">acc</a> <a id="12069" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="12071" class="Symbol">(</a><a id="12072" href="simple_essence.html#11887" class="Bound">x</a> <a id="12074" href="simple_essence.html#9802" class="Field Operator">⊙</a> <a id="12076" href="simple_essence.html#12061" class="Bound">v</a><a id="12077" class="Symbol">)</a> <a id="12079" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="12081" href="simple_essence.html#12061" class="Bound">v</a><a id="12082" class="Symbol">)</a> <a id="12084" href="simple_essence.html#7353" class="Field">𝟘</a> <a id="12086" href="simple_essence.html#9777" class="Field">basisSet</a>
                <a id="12111" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12114" href="simple_essence.html#11165" class="Postulate">x·z≡y·z→x≡y</a> <a id="12126" href="simple_essence.html#10136" class="Field">orthonormal</a> <a id="12138" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="12158" href="simple_essence.html#11887" class="Bound">x</a>
                <a id="12176" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12177" class="Symbol">})</a>
      <a id="12186" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="12188" class="Symbol">λ</a> <a id="12190" class="Symbol">{</a><a id="12191" href="simple_essence.html#12191" class="Bound">lm</a> <a id="12194" class="Symbol">→</a> <a id="12196" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                    <a id="12222" href="simple_essence.html#10864" class="Function">a⊸§←a</a> <a id="12228" class="Symbol">(</a><a id="12229" href="simple_essence.html#10565" class="Function">a⊸§→a</a> <a id="12235" href="simple_essence.html#12191" class="Bound">lm</a><a id="12237" class="Symbol">)</a>
                  <a id="12257" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12281" href="simple_essence.html#10864" class="Function">a⊸§←a</a> <a id="12287" class="Symbol">(</a><a id="12288" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12294" class="Symbol">(λ</a> <a id="12297" href="simple_essence.html#12297" class="Bound">acc</a> <a id="12301" href="simple_essence.html#12301" class="Bound">v</a> <a id="12303" class="Symbol">→</a>
                                     <a id="12342" href="simple_essence.html#12297" class="Bound">acc</a> <a id="12346" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="12348" class="Symbol">(</a><a id="12349" href="simple_essence.html#8060" class="Field">LinMap.f</a> <a id="12358" href="simple_essence.html#12191" class="Bound">lm</a> <a id="12361" href="simple_essence.html#12301" class="Bound">v</a><a id="12362" class="Symbol">)</a> <a id="12364" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="12366" href="simple_essence.html#12301" class="Bound">v</a><a id="12367" class="Symbol">)</a> <a id="12369" href="simple_essence.html#7353" class="Field">𝟘</a> <a id="12371" href="simple_essence.html#9777" class="Field">basisSet</a><a id="12379" class="Symbol">)</a>
                  <a id="12399" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                    <a id="12423" href="simple_essence.html#8043" class="InductiveConstructor">mkLM</a> <a id="12428" class="Symbol">(</a> <a id="12430" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="12436" class="Symbol">(</a> <a id="12438" class="Symbol">λ</a> <a id="12440" href="simple_essence.html#12440" class="Bound">acc</a> <a id="12444" href="simple_essence.html#12444" class="Bound">v</a> <a id="12446" class="Symbol">→</a>
                                     <a id="12485" href="simple_essence.html#12440" class="Bound">acc</a> <a id="12489" href="simple_essence.html#7297" class="Field Operator">+</a> <a id="12491" class="Symbol">(</a><a id="12492" href="simple_essence.html#8060" class="Field">LinMap.f</a> <a id="12501" href="simple_essence.html#12191" class="Bound">lm</a> <a id="12504" href="simple_essence.html#12444" class="Bound">v</a><a id="12505" class="Symbol">)</a> <a id="12507" href="simple_essence.html#7143" class="Field Operator">·</a> <a id="12509" href="simple_essence.html#12444" class="Bound">v</a>
                                 <a id="12544" class="Symbol">)</a> <a id="12546" href="simple_essence.html#7353" class="Field">𝟘</a> <a id="12548" href="simple_essence.html#9777" class="Field">basisSet</a>
                           <a id="12584" href="simple_essence.html#9802" class="Field Operator">⊙_</a>
                         <a id="12612" class="Symbol">)</a> <a id="12614" href="simple_essence.html#9880" class="Field">⊙-distrib-+</a> <a id="12626" href="simple_essence.html#10011" class="Field">⊙-comm-·</a>
                  <a id="12653" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="12656" href="simple_essence.html#8382" class="Postulate">⊸≡</a> <a id="12659" class="Symbol">(</a> <a id="12661" href="simple_essence.html#6444" class="Postulate">extensionality</a>
                            <a id="12704" class="Symbol">(</a> <a id="12706" class="Symbol">λ</a> <a id="12708" href="simple_essence.html#12708" class="Bound">x</a> <a id="12710" class="Symbol">→</a> <a id="12712" href="simple_essence.html#10136" class="Field">orthonormal</a> <a id="12724" class="Symbol">{</a><a id="12725" class="Argument">f</a> <a id="12727" class="Symbol">=</a> <a id="12729" href="simple_essence.html#8060" class="Field">LinMap.f</a> <a id="12738" href="simple_essence.html#12191" class="Bound">lm</a><a id="12740" class="Symbol">}</a> <a id="12742" class="Symbol">{</a><a id="12743" class="Argument">x</a> <a id="12745" class="Symbol">=</a> <a id="12747" href="simple_essence.html#12708" class="Bound">x</a><a id="12748" class="Symbol">}</a> <a id="12750" class="Symbol">)</a>
                        <a id="12776" class="Symbol">)</a>
                   <a id="12797" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                    <a id="12819" href="simple_essence.html#12191" class="Bound">lm</a>
                  <a id="12840" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="12841" class="Symbol">}</a>
      <a id="12849" class="Symbol">)</a>

</pre>
### Stashed

Stashed coding attempts.

<pre class="Agda"><a id="12904" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="12987" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="13049" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="13143" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="13206" class="Comment">--</a>
<a id="13209" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="13232" class="Comment">--         ⦃_ : Additive A⦄ ⦃_ : Scalable A⦄</a>
<a id="13277" class="Comment">--         ⦃_ : VectorSpace A⦄</a>
<a id="13308" class="Comment">--         -------------------------------------</a>
<a id="13357" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="13385" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

<a id="13417" class="Comment">-- -- f(0) = 0</a>
<a id="13432" class="Comment">-- zero-lin : {A B : Set a}</a>
<a id="13460" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13511" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13562" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>

<a id="13595" class="Comment">-- -- Injectivity of linear function</a>
<a id="13632" class="Comment">-- inj-lin : {A B : Set a} {x y : A}</a>
<a id="13669" class="Comment">--           ⦃ _ : Additive A ⦄ ⦃ _ : Additive B ⦄</a>
<a id="13720" class="Comment">--           ⦃ _ : Scalable A ⦄ ⦃ _ : Scalable B ⦄</a>
<a id="13771" class="Comment">--           ⦃ _ : LinMap A B ⦄</a>
<a id="13803" class="Comment">--        → LinMap.f _ x ≡ LinMap.f _ y</a>
<a id="13843" class="Comment">--           ---------------------------</a>
<a id="13884" class="Comment">--        → x ≡ y</a>
<a id="13902" class="Comment">-- inj-lin {x = x} {y = y} fx≡fy =</a>
<a id="13937" class="Comment">--   let f = LinMap.f _</a>
<a id="13961" class="Comment">--    in begin</a>
<a id="13976" class="Comment">--         x</a>
<a id="13989" class="Comment">--       ≡⟨⟩</a>
<a id="14002" class="Comment">--         f (x - y)</a>
<a id="14023" class="Comment">--       ≡⟨ LinMap.adds _ ⟩</a>
<a id="14051" class="Comment">--         f x - f y</a>
<a id="14072" class="Comment">--       ≡⟨ sub-≡ fx≡fy ⟩</a>
<a id="14098" class="Comment">--         0</a>
<a id="14111" class="Comment">--       ≡⟨⟩</a>
<a id="14124" class="Comment">--         y</a>
<a id="14137" class="Comment">--       ∎</a>
      
<a id="14155" class="Comment">-- cong-app′ : ∀ {A : Set a} {B : Set b} {f : A → B} {x y : A}</a>
<a id="14218" class="Comment">--          → f x ≡ f y</a>
<a id="14242" class="Comment">--             ---------</a>
<a id="14267" class="Comment">--          → x ≡ y</a>
<a id="14287" class="Comment">-- cong-app′ fx≡fy = {!contraposition!}</a>
         
<a id="14337" class="Comment">-- x·z≡y·z→x≡y : {A : Set a}</a>
<a id="14366" class="Comment">--                ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="14422" class="Comment">--                ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="14481" class="Comment">--                {x y : A}</a>
<a id="14509" class="Comment">--             → (∀ {z : A} → x · z ≡ y · z)</a>
<a id="14554" class="Comment">--                ------------------------------------------------------------</a>
<a id="14633" class="Comment">--             → x ≡ y</a>
<a id="14656" class="Comment">-- x·z≡y·z→x≡y {x = x} {y = y} g =</a>
<a id="14691" class="Comment">--   let f = LinMap.f _</a>
<a id="14715" class="Comment">--       z = foldl (λ acc v → acc ⊕ f v ⊛ v) id⊕ basisSet</a>
<a id="14773" class="Comment">--       x·z≡y·z = g {z}</a>
<a id="14798" class="Comment">--    in cong-app refl {!!}</a>
<a id="14826" class="Comment">--    -- in begin</a>
<a id="14844" class="Comment">--    --      -- ?</a>
<a id="14863" class="Comment">--    --      x·z≡y·z</a>
<a id="14885" class="Comment">--    --    -- ≡⟨ ? ⟩</a>
<a id="14907" class="Comment">--    --    --   x · z ≡ y · z</a>
<a id="14938" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="14957" class="Comment">--    --    -- ≡⟨ cong (_≡ y · z) comm-· ⟩</a>
<a id="15000" class="Comment">--    --      z · x ≡ y · z</a>
<a id="15028" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15047" class="Comment">--    --    -- ≡⟨ cong (z · x ≡_) comm-· ⟩</a>
<a id="15090" class="Comment">--    --      z · x ≡ z · y</a>
<a id="15118" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15137" class="Comment">--    --    -- ≡⟨ cong (_≡ z · y) (orthonormal) ⟩</a>
<a id="15187" class="Comment">--    --      f x ≡ z · y</a>
<a id="15213" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15232" class="Comment">--    --    -- ≡⟨ cong (f x ≡_) (orthonormal) ⟩</a>
<a id="15280" class="Comment">--    --      f x ≡ f y</a>
<a id="15304" class="Comment">--    --    ≡⟨ ? ⟩</a>
<a id="15323" class="Comment">--    --    -- ≡⟨ cong-app ⟩</a>
<a id="15352" class="Comment">--    --      x ≡ y</a>
<a id="15372" class="Comment">--    --    ∎</a>

<a id="15387" class="Comment">-- -- So, how was Agsy able to jump over all of that?</a>
<a id="15441" class="Comment">-- -- My usual experience w/ Agsy is that when I ask it to solve anything</a>
<a id="15515" class="Comment">-- -- non-trivial by itself it always complains, &quot;Sorry, I don&#39;t support</a>
<a id="15588" class="Comment">-- -- literals, yet.&quot;, which I&#39;ve never understood.</a>

<a id="15641" class="Comment">-- a⊸§↔a : {A : Set a}</a>
<a id="15664" class="Comment">--          ⦃ _ : Additive A ⦄ ⦃ _ : Scalable A ⦄</a>
<a id="15714" class="Comment">--          ⦃ _ : VectorSpace A ⦄ ⦃ _ : LinMap A § ⦄</a>
<a id="15767" class="Comment">--          -----------------------------------------</a>
<a id="15821" class="Comment">--       → (LinMap A §) ↔ A</a>
<a id="15849" class="Comment">-- a⊸§↔a {A} =</a>
<a id="15864" class="Comment">--   mk↔ {f = a⊸§→a} {f⁻¹ = a⊸§←a}</a>
<a id="15899" class="Comment">--       ( (λ {x → begin</a>
<a id="15924" class="Comment">--                   a⊸§→a (a⊸§←a x)</a>
<a id="15961" class="Comment">--                 ≡⟨⟩</a>
<a id="15984" class="Comment">--                   a⊸§→a (mkLM (x ·_) ·-distrib-⊕ ·-comm-⊛)</a>
<a id="16046" class="Comment">--                 ≡⟨⟩</a>
<a id="16069" class="Comment">--                   foldl (λ acc v → acc ⊕ (x · v) ⊛ v) id⊕ basisSet</a>
<a id="16139" class="Comment">--                 ≡⟨ x·z≡y·z→x≡y (orthonormal {f = (x ·_)}) ⟩</a>
<a id="16202" class="Comment">--                   x</a>
<a id="16225" class="Comment">--                 ∎})</a>
<a id="16248" class="Comment">--       , λ {lm → begin</a>
<a id="16273" class="Comment">--                   a⊸§←a (a⊸§→a lm)</a>
<a id="16311" class="Comment">--                 ≡⟨⟩</a>
<a id="16334" class="Comment">--                   a⊸§←a (foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)</a>
<a id="16420" class="Comment">--                 ≡⟨⟩</a>
<a id="16443" class="Comment">--                   mkLM ((foldl (λ acc v → acc ⊕ (LinMap.f lm v) ⊛ v) id⊕ basisSet)·_)</a>
<a id="16532" class="Comment">--                        ·-distrib-⊕ ·-comm-⊛</a>
<a id="16579" class="Comment">--                 ≡⟨ ⊸≡ ( extensionality</a>
<a id="16621" class="Comment">--                           ( λ x → orthonormal {f = LinMap.f lm} {x = x} )</a>
<a id="16698" class="Comment">--                       )</a>
<a id="16725" class="Comment">--                  ⟩</a>
<a id="16747" class="Comment">--                   lm</a>
<a id="16771" class="Comment">--                 ∎}</a>
<a id="16793" class="Comment">--       )</a>


</pre>