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
                  {{_ : Additive A}} {{_ : Additive B}}
                  {{_ : Scalable A}} {{_ : Scalable B}}
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
    a⊸§≃a : ∀ {A : Set} {{_ : Additive A}} {{_ : Scalable A}}
            -------------------------------------------------
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

<pre class="Agda"><a id="5499" class="Keyword">module</a> <a id="5506" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5521" class="Symbol">{</a><a id="5522" href="simple_essence.html#5522" class="Bound">s</a> <a id="5524" href="simple_essence.html#5524" class="Bound">a</a> <a id="5526" href="simple_essence.html#5526" class="Bound">b</a><a id="5527" class="Symbol">}</a> <a id="5529" class="Keyword">where</a>

<a id="5536" class="Keyword">open</a> <a id="5541" class="Keyword">import</a> <a id="5548" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5567" class="Keyword">open</a> <a id="5572" class="Keyword">import</a> <a id="5579" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5614" class="Keyword">using</a> <a id="5620" class="Symbol">(</a><a id="5621" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5635" class="Symbol">)</a>
<a id="5637" class="Keyword">open</a> <a id="5642" class="Keyword">import</a> <a id="5649" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5660" class="Keyword">open</a> <a id="5665" class="Keyword">import</a> <a id="5672" href="Data.List.html" class="Module">Data.List</a>
<a id="5682" class="Keyword">open</a> <a id="5687" class="Keyword">import</a> <a id="5694" href="Function.html" class="Module">Function</a> <a id="5703" class="Keyword">using</a> <a id="5709" class="Symbol">(</a><a id="5710" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5713" class="Symbol">;</a> <a id="5715" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5718" class="Symbol">;</a> <a id="5720" href="Function.Base.html#615" class="Function">id</a><a id="5722" class="Symbol">)</a>
<a id="5724" class="Keyword">open</a> <a id="5729" class="Keyword">import</a> <a id="5736" href="Level.html" class="Module">Level</a> <a id="5742" class="Keyword">using</a> <a id="5748" class="Symbol">(</a><a id="5749" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5754" class="Symbol">;</a> <a id="5756" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5759" class="Symbol">)</a>

<a id="5762" class="Keyword">import</a> <a id="5769" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5807" class="Symbol">as</a> <a id="5810" class="Module">Eq</a>
<a id="5813" class="Keyword">open</a> <a id="5818" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5821" class="Keyword">using</a> <a id="5827" class="Symbol">(</a><a id="5828" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5831" class="Symbol">;</a> <a id="5833" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5837" class="Symbol">;</a> <a id="5839" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5844" class="Symbol">;</a> <a id="5846" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5849" class="Symbol">;</a> <a id="5851" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5855" class="Symbol">;</a> <a id="5857" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5862" class="Symbol">;</a> <a id="5864" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5872" class="Symbol">;</a> <a id="5874" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5879" class="Symbol">)</a>
<a id="5881" class="Keyword">open</a> <a id="5886" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5901" class="Keyword">using</a> <a id="5907" class="Symbol">(</a><a id="5908" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5914" class="Symbol">;</a> <a id="5916" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5921" class="Symbol">;</a> <a id="5923" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5929" class="Symbol">;</a> <a id="5931" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5933" class="Symbol">)</a>

<a id="5936" class="Keyword">postulate</a>
  <a id="5948" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="6023" href="simple_essence.html#6023" class="Postulate">id+</a> <a id="6027" class="Symbol">:</a> <a id="6029" class="Symbol">{</a><a id="6030" href="simple_essence.html#6030" class="Bound">x</a> <a id="6032" class="Symbol">:</a> <a id="6034" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="6039" class="Symbol">}</a> <a id="6041" class="Symbol">→</a> <a id="6043" class="Number">0.0</a> <a id="6047" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6049" href="simple_essence.html#6030" class="Bound">x</a> <a id="6051" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6053" href="simple_essence.html#6030" class="Bound">x</a>
  <a id="extensionality"></a><a id="6057" href="simple_essence.html#6057" class="Postulate">extensionality</a> <a id="6072" class="Symbol">:</a> <a id="6074" class="Symbol">∀</a> <a id="6076" class="Symbol">{</a><a id="6077" href="simple_essence.html#6077" class="Bound">ℓ₁</a> <a id="6080" href="simple_essence.html#6080" class="Bound">ℓ₂</a><a id="6082" class="Symbol">}</a> <a id="6084" class="Symbol">→</a> <a id="6086" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="6101" href="simple_essence.html#6077" class="Bound">ℓ₁</a> <a id="6104" href="simple_essence.html#6080" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="6108" href="simple_essence.html#6108" class="Function">ℓ</a> <a id="6110" class="Symbol">:</a> <a id="6112" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="6118" href="simple_essence.html#6108" class="Function">ℓ</a> <a id="6120" class="Symbol">=</a> <a id="6122" href="simple_essence.html#5522" class="Bound">s</a> <a id="6124" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6126" href="simple_essence.html#5524" class="Bound">a</a> <a id="6128" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="6130" href="simple_essence.html#5526" class="Bound">b</a>

<a id="6133" class="Keyword">data</a> <a id="§"></a><a id="6138" href="simple_essence.html#6138" class="Datatype">§</a> <a id="6140" class="Symbol">:</a> <a id="6142" class="PrimitiveType">Set</a> <a id="6146" href="simple_essence.html#5524" class="Bound">a</a> <a id="6148" class="Keyword">where</a>
  <a id="§.S"></a><a id="6156" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6158" class="Symbol">:</a> <a id="6160" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="6166" class="Symbol">→</a> <a id="6168" href="simple_essence.html#6138" class="Datatype">§</a>

<a id="6171" class="Keyword">record</a> <a id="Additive"></a><a id="6178" href="simple_essence.html#6178" class="Record">Additive</a> <a id="6187" class="Symbol">(</a><a id="6188" href="simple_essence.html#6188" class="Bound">A</a> <a id="6190" class="Symbol">:</a> <a id="6192" class="PrimitiveType">Set</a> <a id="6196" href="simple_essence.html#5524" class="Bound">a</a><a id="6197" class="Symbol">)</a> <a id="6199" class="Symbol">:</a> <a id="6201" class="PrimitiveType">Set</a> <a id="6205" href="simple_essence.html#6108" class="Function">ℓ</a> <a id="6207" class="Keyword">where</a>
  <a id="6215" class="Keyword">infixl</a> <a id="6222" class="Number">6</a> <a id="6224" href="simple_essence.html#6304" class="Field Operator">_⊕_</a>  <a id="6229" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6281" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6291" href="simple_essence.html#6291" class="Field">id⊕</a>  <a id="6296" class="Symbol">:</a> <a id="6298" href="simple_essence.html#6188" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6304" href="simple_essence.html#6304" class="Field Operator">_⊕_</a>  <a id="6309" class="Symbol">:</a> <a id="6311" href="simple_essence.html#6188" class="Bound">A</a> <a id="6313" class="Symbol">→</a> <a id="6315" href="simple_essence.html#6188" class="Bound">A</a> <a id="6317" class="Symbol">→</a> <a id="6319" href="simple_essence.html#6188" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6325" href="simple_essence.html#6325" class="Field">id-⊕</a> <a id="6330" class="Symbol">:</a> <a id="6332" class="Symbol">(</a><a id="6333" href="simple_essence.html#6333" class="Bound">a</a> <a id="6335" class="Symbol">:</a> <a id="6337" href="simple_essence.html#6188" class="Bound">A</a><a id="6338" class="Symbol">)</a>
           <a id="6351" class="Comment">-----------</a>
         <a id="6372" class="Symbol">→</a> <a id="6374" href="simple_essence.html#6291" class="Field">id⊕</a> <a id="6378" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="6380" href="simple_essence.html#6333" class="Bound">a</a> <a id="6382" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6384" href="simple_essence.html#6333" class="Bound">a</a>
    <a id="6390" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6443" class="Keyword">open</a> <a id="6448" href="simple_essence.html#6178" class="Module">Additive</a> <a id="6457" class="Symbol">{{</a> <a id="6460" class="Symbol">...</a> <a id="6464" class="Symbol">}}</a>
<a id="6467" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6478" href="simple_essence.html#6478" class="Function">AdditiveScalar</a> <a id="6493" class="Symbol">:</a> <a id="6495" href="simple_essence.html#6178" class="Record">Additive</a> <a id="6504" href="simple_essence.html#6138" class="Datatype">§</a>
  <a id="6508" href="simple_essence.html#6478" class="Function">AdditiveScalar</a> <a id="6523" class="Symbol">=</a> <a id="6525" class="Keyword">record</a>
    <a id="6536" class="Symbol">{</a> <a id="6538" href="simple_essence.html#6291" class="Field">id⊕</a>  <a id="6543" class="Symbol">=</a> <a id="6545" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6547" class="Number">0.0</a>
    <a id="6555" class="Symbol">;</a> <a id="6557" href="simple_essence.html#6304" class="Field Operator">_⊕_</a>  <a id="6562" class="Symbol">=</a> <a id="6564" class="Symbol">λ</a> <a id="6566" class="Symbol">{(</a><a id="6568" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6570" href="simple_essence.html#6570" class="Bound">x</a><a id="6571" class="Symbol">)</a> <a id="6573" class="Symbol">(</a><a id="6574" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6576" href="simple_essence.html#6576" class="Bound">y</a><a id="6577" class="Symbol">)</a> <a id="6579" class="Symbol">→</a> <a id="6581" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6583" class="Symbol">(</a><a id="6584" href="simple_essence.html#6570" class="Bound">x</a> <a id="6586" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6588" href="simple_essence.html#6576" class="Bound">y</a><a id="6589" class="Symbol">)}</a>
    <a id="6596" class="Symbol">;</a> <a id="6598" href="simple_essence.html#6325" class="Field">id-⊕</a> <a id="6603" class="Symbol">=</a> <a id="6605" class="Symbol">λ</a> <a id="6607" class="Symbol">{</a> <a id="6609" class="Symbol">(</a><a id="6610" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6612" href="simple_essence.html#6612" class="Bound">x</a><a id="6613" class="Symbol">)</a> <a id="6615" class="Symbol">→</a> <a id="6617" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6650" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6652" class="Symbol">(</a><a id="6653" class="Number">0.0</a> <a id="6657" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6659" href="simple_essence.html#6612" class="Bound">x</a><a id="6660" class="Symbol">)</a>
                         <a id="6687" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6690" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6695" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6697" href="simple_essence.html#6023" class="Postulate">id+</a> <a id="6701" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6730" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="6732" href="simple_essence.html#6612" class="Bound">x</a>
                         <a id="6759" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6776" class="Symbol">}</a>
    <a id="6782" class="Symbol">}</a>

<a id="6785" class="Keyword">record</a> <a id="Scalable"></a><a id="6792" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="6801" class="Symbol">(</a><a id="6802" href="simple_essence.html#6802" class="Bound">A</a> <a id="6804" class="Symbol">:</a> <a id="6806" class="PrimitiveType">Set</a> <a id="6810" href="simple_essence.html#5524" class="Bound">a</a><a id="6811" class="Symbol">)</a> <a id="6813" class="Symbol">:</a> <a id="6815" class="PrimitiveType">Set</a> <a id="6819" href="simple_essence.html#6108" class="Function">ℓ</a> <a id="6821" class="Keyword">where</a>
  <a id="6829" class="Keyword">infixl</a> <a id="6836" class="Number">7</a> <a id="6838" href="simple_essence.html#6905" class="Field Operator">_⊛_</a>  <a id="6843" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6895" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6905" href="simple_essence.html#6905" class="Field Operator">_⊛_</a> <a id="6909" class="Symbol">:</a> <a id="6911" href="simple_essence.html#6138" class="Datatype">§</a> <a id="6913" class="Symbol">→</a> <a id="6915" href="simple_essence.html#6802" class="Bound">A</a> <a id="6917" class="Symbol">→</a> <a id="6919" href="simple_essence.html#6802" class="Bound">A</a>
<a id="6921" class="Keyword">open</a> <a id="6926" href="simple_essence.html#6792" class="Module">Scalable</a> <a id="6935" class="Symbol">{{</a> <a id="6938" class="Symbol">...</a> <a id="6942" class="Symbol">}}</a>
<a id="6945" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="6956" href="simple_essence.html#6956" class="Function">ScalableScalar</a> <a id="6971" class="Symbol">:</a> <a id="6973" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="6982" href="simple_essence.html#6138" class="Datatype">§</a>
  <a id="6986" href="simple_essence.html#6956" class="Function">ScalableScalar</a> <a id="7001" class="Symbol">=</a> <a id="7003" class="Keyword">record</a>
    <a id="7014" class="Symbol">{</a> <a id="7016" href="simple_essence.html#6905" class="Field Operator">_⊛_</a> <a id="7020" class="Symbol">=</a> <a id="7022" class="Symbol">λ</a> <a id="7024" class="Symbol">{(</a><a id="7026" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="7028" href="simple_essence.html#7028" class="Bound">x</a><a id="7029" class="Symbol">)</a> <a id="7031" class="Symbol">(</a><a id="7032" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="7034" href="simple_essence.html#7034" class="Bound">y</a><a id="7035" class="Symbol">)</a> <a id="7037" class="Symbol">→</a> <a id="7039" href="simple_essence.html#6156" class="InductiveConstructor">S</a> <a id="7041" class="Symbol">(</a><a id="7042" href="simple_essence.html#7028" class="Bound">x</a> <a id="7044" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="7046" href="simple_essence.html#7034" class="Bound">y</a><a id="7047" class="Symbol">)}</a>
    <a id="7054" class="Symbol">}</a>

<a id="7057" class="Keyword">record</a> <a id="LinMap"></a><a id="7064" href="simple_essence.html#7064" class="Record">LinMap</a> <a id="7071" class="Symbol">(</a><a id="7072" href="simple_essence.html#7072" class="Bound">A</a> <a id="7074" class="Symbol">:</a> <a id="7076" class="PrimitiveType">Set</a> <a id="7080" href="simple_essence.html#5524" class="Bound">a</a><a id="7081" class="Symbol">)</a> <a id="7083" class="Symbol">(</a><a id="7084" href="simple_essence.html#7084" class="Bound">B</a> <a id="7086" class="Symbol">:</a> <a id="7088" class="PrimitiveType">Set</a> <a id="7092" href="simple_essence.html#5524" class="Bound">a</a><a id="7093" class="Symbol">)</a>
              <a id="7109" class="Symbol">{{</a><a id="7111" href="simple_essence.html#7111" class="Bound">_</a> <a id="7113" class="Symbol">:</a> <a id="7115" href="simple_essence.html#6178" class="Record">Additive</a> <a id="7124" href="simple_essence.html#7072" class="Bound">A</a><a id="7125" class="Symbol">}}</a> <a id="7128" class="Symbol">{{</a><a id="7130" href="simple_essence.html#7130" class="Bound">_</a> <a id="7132" class="Symbol">:</a> <a id="7134" href="simple_essence.html#6178" class="Record">Additive</a> <a id="7143" href="simple_essence.html#7084" class="Bound">B</a><a id="7144" class="Symbol">}}</a>
              <a id="7161" class="Symbol">{{</a><a id="7163" href="simple_essence.html#7163" class="Bound">_</a> <a id="7165" class="Symbol">:</a> <a id="7167" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="7176" href="simple_essence.html#7072" class="Bound">A</a><a id="7177" class="Symbol">}}</a> <a id="7180" class="Symbol">{{</a><a id="7182" href="simple_essence.html#7182" class="Bound">_</a> <a id="7184" class="Symbol">:</a> <a id="7186" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="7195" href="simple_essence.html#7084" class="Bound">B</a><a id="7196" class="Symbol">}}</a>
              <a id="7213" class="Symbol">:</a> <a id="7215" class="PrimitiveType">Set</a> <a id="7219" href="simple_essence.html#6108" class="Function">ℓ</a> <a id="7221" class="Keyword">where</a>
  <a id="7229" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7241" href="simple_essence.html#7241" class="InductiveConstructor">mkLM</a>
  <a id="7248" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7258" href="simple_essence.html#7258" class="Field">f</a>      <a id="7265" class="Symbol">:</a> <a id="7267" href="simple_essence.html#7072" class="Bound">A</a> <a id="7269" class="Symbol">→</a> <a id="7271" href="simple_essence.html#7084" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7278" href="simple_essence.html#7278" class="Field">adds</a>   <a id="7285" class="Symbol">:</a> <a id="7287" class="Symbol">∀</a> <a id="7289" class="Symbol">{</a><a id="7290" href="simple_essence.html#7290" class="Bound">a</a> <a id="7292" href="simple_essence.html#7292" class="Bound">b</a> <a id="7294" class="Symbol">:</a> <a id="7296" href="simple_essence.html#7072" class="Bound">A</a><a id="7297" class="Symbol">}</a>
             <a id="7312" class="Comment">---------------------</a>
           <a id="7345" class="Symbol">→</a> <a id="7347" href="simple_essence.html#7258" class="Field">f</a> <a id="7349" class="Symbol">(</a><a id="7350" href="simple_essence.html#7290" class="Bound">a</a> <a id="7352" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="7354" href="simple_essence.html#7292" class="Bound">b</a><a id="7355" class="Symbol">)</a> <a id="7357" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7359" href="simple_essence.html#7258" class="Field">f</a> <a id="7361" href="simple_essence.html#7290" class="Bound">a</a> <a id="7363" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="7365" href="simple_essence.html#7258" class="Field">f</a> <a id="7367" href="simple_essence.html#7292" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7374" href="simple_essence.html#7374" class="Field">scales</a> <a id="7381" class="Symbol">:</a> <a id="7383" class="Symbol">∀</a> <a id="7385" class="Symbol">{</a><a id="7386" href="simple_essence.html#7386" class="Bound">s</a> <a id="7388" class="Symbol">:</a> <a id="7390" href="simple_essence.html#6138" class="Datatype">§</a><a id="7391" class="Symbol">}</a> <a id="7393" class="Symbol">{</a><a id="7394" href="simple_essence.html#7394" class="Bound">a</a> <a id="7396" class="Symbol">:</a> <a id="7398" href="simple_essence.html#7072" class="Bound">A</a><a id="7399" class="Symbol">}</a>
             <a id="7414" class="Comment">-------------------</a>
           <a id="7445" class="Symbol">→</a> <a id="7447" href="simple_essence.html#7258" class="Field">f</a> <a id="7449" class="Symbol">(</a><a id="7450" href="simple_essence.html#7386" class="Bound">s</a> <a id="7452" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="7454" href="simple_essence.html#7394" class="Bound">a</a><a id="7455" class="Symbol">)</a> <a id="7457" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7459" href="simple_essence.html#7386" class="Bound">s</a> <a id="7461" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="7463" href="simple_essence.html#7258" class="Field">f</a> <a id="7465" href="simple_essence.html#7394" class="Bound">a</a>
<a id="7467" class="Keyword">open</a> <a id="7472" href="simple_essence.html#7064" class="Module">LinMap</a> <a id="7479" class="Symbol">{{</a> <a id="7482" class="Symbol">...</a> <a id="7486" class="Symbol">}}</a>

<a id="7490" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7516" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7564" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7576" href="simple_essence.html#7576" class="Postulate">⊸≡</a> <a id="7579" class="Symbol">:</a> <a id="7581" class="Symbol">{</a><a id="7582" href="simple_essence.html#7582" class="Bound">A</a> <a id="7584" href="simple_essence.html#7584" class="Bound">B</a> <a id="7586" class="Symbol">:</a> <a id="7588" class="PrimitiveType">Set</a> <a id="7592" href="simple_essence.html#5524" class="Bound">a</a><a id="7593" class="Symbol">}</a>
       <a id="7602" class="Symbol">{{</a><a id="7604" href="simple_essence.html#7604" class="Bound">_</a> <a id="7606" class="Symbol">:</a> <a id="7608" href="simple_essence.html#6178" class="Record">Additive</a> <a id="7617" href="simple_essence.html#7582" class="Bound">A</a><a id="7618" class="Symbol">}}</a> <a id="7621" class="Symbol">{{</a><a id="7623" href="simple_essence.html#7623" class="Bound">_</a> <a id="7625" class="Symbol">:</a> <a id="7627" href="simple_essence.html#6178" class="Record">Additive</a> <a id="7636" href="simple_essence.html#7584" class="Bound">B</a><a id="7637" class="Symbol">}}</a>
       <a id="7647" class="Symbol">{{</a><a id="7649" href="simple_essence.html#7649" class="Bound">_</a> <a id="7651" class="Symbol">:</a> <a id="7653" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="7662" href="simple_essence.html#7582" class="Bound">A</a><a id="7663" class="Symbol">}}</a> <a id="7666" class="Symbol">{{</a><a id="7668" href="simple_essence.html#7668" class="Bound">_</a> <a id="7670" class="Symbol">:</a> <a id="7672" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="7681" href="simple_essence.html#7584" class="Bound">B</a><a id="7682" class="Symbol">}}</a>
       <a id="7692" class="Symbol">{</a><a id="7693" href="simple_essence.html#7693" class="Bound">lm₁</a> <a id="7697" href="simple_essence.html#7697" class="Bound">lm₂</a> <a id="7701" class="Symbol">:</a> <a id="7703" href="simple_essence.html#7064" class="Record">LinMap</a> <a id="7710" href="simple_essence.html#7582" class="Bound">A</a> <a id="7712" href="simple_essence.html#7584" class="Bound">B</a><a id="7713" class="Symbol">}</a>
     <a id="7720" class="Symbol">→</a> <a id="7722" href="simple_essence.html#7258" class="Field">LinMap.f</a> <a id="7731" href="simple_essence.html#7693" class="Bound">lm₁</a> <a id="7735" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7737" href="simple_essence.html#7258" class="Field">LinMap.f</a> <a id="7746" href="simple_essence.html#7697" class="Bound">lm₂</a>
       <a id="7757" class="Comment">---------------------------</a>
     <a id="7790" class="Symbol">→</a> <a id="7792" href="simple_essence.html#7693" class="Bound">lm₁</a> <a id="7796" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7798" href="simple_essence.html#7697" class="Bound">lm₂</a>

<a id="7803" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7810" href="simple_essence.html#7810" class="Record">VectorSpace</a> <a id="7822" class="Symbol">(</a><a id="7823" href="simple_essence.html#7823" class="Bound">A</a> <a id="7825" class="Symbol">:</a> <a id="7827" class="PrimitiveType">Set</a> <a id="7831" href="simple_essence.html#5524" class="Bound">a</a><a id="7832" class="Symbol">)</a>
                   <a id="7853" class="Symbol">{{</a><a id="7855" href="simple_essence.html#7855" class="Bound">_</a> <a id="7857" class="Symbol">:</a> <a id="7859" href="simple_essence.html#6178" class="Record">Additive</a> <a id="7868" href="simple_essence.html#7823" class="Bound">A</a><a id="7869" class="Symbol">}}</a> <a id="7872" class="Symbol">{{</a><a id="7874" href="simple_essence.html#7874" class="Bound">_</a> <a id="7876" class="Symbol">:</a> <a id="7878" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="7887" href="simple_essence.html#7823" class="Bound">A</a><a id="7888" class="Symbol">}}</a>
                   <a id="7910" class="Symbol">:</a> <a id="7912" class="PrimitiveType">Set</a> <a id="7916" href="simple_essence.html#6108" class="Function">ℓ</a> <a id="7918" class="Keyword">where</a>
  <a id="7926" class="Keyword">field</a>
    <a id="7936" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="8030" href="simple_essence.html#8030" class="Field">basisSet</a>    <a id="8042" class="Symbol">:</a> <a id="8044" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="8049" href="simple_essence.html#7823" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="8055" href="simple_essence.html#8055" class="Field Operator">_·_</a>         <a id="8067" class="Symbol">:</a> <a id="8069" href="simple_essence.html#7823" class="Bound">A</a> <a id="8071" class="Symbol">→</a> <a id="8073" href="simple_essence.html#7823" class="Bound">A</a> <a id="8075" class="Symbol">→</a> <a id="8077" href="simple_essence.html#6138" class="Datatype">§</a>
    <a id="8083" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="8133" href="simple_essence.html#8133" class="Field">·-distrib-⊕</a> <a id="8145" class="Symbol">:</a> <a id="8147" class="Symbol">∀</a> <a id="8149" class="Symbol">{</a><a id="8150" href="simple_essence.html#8150" class="Bound">a</a> <a id="8152" href="simple_essence.html#8152" class="Bound">b</a> <a id="8154" href="simple_essence.html#8154" class="Bound">c</a> <a id="8156" class="Symbol">:</a> <a id="8158" href="simple_essence.html#7823" class="Bound">A</a><a id="8159" class="Symbol">}</a>
                  <a id="8179" class="Comment">-------------------------------</a>
                <a id="8227" class="Symbol">→</a> <a id="8229" href="simple_essence.html#8150" class="Bound">a</a> <a id="8231" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="8233" class="Symbol">(</a><a id="8234" href="simple_essence.html#8152" class="Bound">b</a> <a id="8236" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="8238" href="simple_essence.html#8154" class="Bound">c</a><a id="8239" class="Symbol">)</a> <a id="8241" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8243" class="Symbol">(</a><a id="8244" href="simple_essence.html#8150" class="Bound">a</a> <a id="8246" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="8248" href="simple_essence.html#8152" class="Bound">b</a><a id="8249" class="Symbol">)</a> <a id="8251" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="8253" class="Symbol">(</a><a id="8254" href="simple_essence.html#8150" class="Bound">a</a> <a id="8256" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="8258" href="simple_essence.html#8154" class="Bound">c</a><a id="8259" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8265" href="simple_essence.html#8265" class="Field">·-comm-⊛</a>    <a id="8277" class="Symbol">:</a> <a id="8279" class="Symbol">∀</a> <a id="8281" class="Symbol">{</a><a id="8282" href="simple_essence.html#8282" class="Bound">s</a> <a id="8284" class="Symbol">:</a> <a id="8286" href="simple_essence.html#6138" class="Datatype">§</a><a id="8287" class="Symbol">}</a> <a id="8289" class="Symbol">{</a><a id="8290" href="simple_essence.html#8290" class="Bound">a</a> <a id="8292" href="simple_essence.html#8292" class="Bound">b</a> <a id="8294" class="Symbol">:</a> <a id="8296" href="simple_essence.html#7823" class="Bound">A</a><a id="8297" class="Symbol">}</a>
                  <a id="8317" class="Comment">-------------------------</a>
                <a id="8359" class="Symbol">→</a> <a id="8361" href="simple_essence.html#8290" class="Bound">a</a> <a id="8363" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="8365" class="Symbol">(</a><a id="8366" href="simple_essence.html#8282" class="Bound">s</a> <a id="8368" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="8370" href="simple_essence.html#8292" class="Bound">b</a><a id="8371" class="Symbol">)</a> <a id="8373" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8375" href="simple_essence.html#8282" class="Bound">s</a> <a id="8377" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="8379" class="Symbol">(</a><a id="8380" href="simple_essence.html#8290" class="Bound">a</a> <a id="8382" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="8384" href="simple_essence.html#8292" class="Bound">b</a><a id="8385" class="Symbol">)</a>
    <a id="8391" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8475" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8533" href="simple_essence.html#8533" class="Field">orthonormal</a> <a id="8545" class="Symbol">:</a> <a id="8547" class="Symbol">∀</a> <a id="8549" class="Symbol">{</a><a id="8550" href="simple_essence.html#8550" class="Bound">f</a> <a id="8552" class="Symbol">:</a> <a id="8554" href="simple_essence.html#7823" class="Bound">A</a> <a id="8556" class="Symbol">→</a> <a id="8558" href="simple_essence.html#6138" class="Datatype">§</a><a id="8559" class="Symbol">}</a>
                <a id="8577" class="Symbol">→</a> <a id="8579" class="Symbol">{</a><a id="8580" href="simple_essence.html#8580" class="Bound">x</a> <a id="8582" class="Symbol">:</a> <a id="8584" href="simple_essence.html#7823" class="Bound">A</a><a id="8585" class="Symbol">}</a>
                  <a id="8605" class="Comment">----------------------------------------------------------</a>
                <a id="8680" class="Symbol">→</a> <a id="8682" class="Symbol">(</a><a id="8683" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8689" class="Symbol">(λ</a> <a id="8692" href="simple_essence.html#8692" class="Bound">acc</a> <a id="8696" href="simple_essence.html#8696" class="Bound">v</a> <a id="8698" class="Symbol">→</a> <a id="8700" href="simple_essence.html#8692" class="Bound">acc</a> <a id="8704" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="8706" class="Symbol">(</a><a id="8707" href="simple_essence.html#8550" class="Bound">f</a> <a id="8709" href="simple_essence.html#8696" class="Bound">v</a><a id="8710" class="Symbol">)</a> <a id="8712" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="8714" href="simple_essence.html#8696" class="Bound">v</a><a id="8715" class="Symbol">)</a> <a id="8717" href="simple_essence.html#6291" class="Field">id⊕</a> <a id="8721" href="simple_essence.html#8030" class="Field">basisSet</a><a id="8729" class="Symbol">)</a> <a id="8731" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="8733" href="simple_essence.html#8580" class="Bound">x</a> <a id="8735" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8737" href="simple_essence.html#8550" class="Bound">f</a> <a id="8739" href="simple_essence.html#8580" class="Bound">x</a>
<a id="8741" class="Keyword">open</a> <a id="8746" href="simple_essence.html#7810" class="Module">VectorSpace</a> <a id="8758" class="Symbol">{{</a> <a id="8761" class="Symbol">...</a> <a id="8765" class="Symbol">}}</a>

<a id="8769" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8809" href="simple_essence.html#8809" class="Function">a⊸§→a</a> <a id="8815" class="Symbol">:</a> <a id="8817" class="Symbol">{</a><a id="8818" href="simple_essence.html#8818" class="Bound">A</a> <a id="8820" class="Symbol">:</a> <a id="8822" class="PrimitiveType">Set</a> <a id="8826" href="simple_essence.html#5524" class="Bound">a</a><a id="8827" class="Symbol">}</a>
        <a id="8837" class="Symbol">{{</a><a id="8839" href="simple_essence.html#8839" class="Bound">_</a> <a id="8841" class="Symbol">:</a> <a id="8843" href="simple_essence.html#6178" class="Record">Additive</a> <a id="8852" href="simple_essence.html#8818" class="Bound">A</a><a id="8853" class="Symbol">}}</a> <a id="8856" class="Symbol">{{</a><a id="8858" href="simple_essence.html#8858" class="Bound">_</a> <a id="8860" class="Symbol">:</a> <a id="8862" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="8871" href="simple_essence.html#8818" class="Bound">A</a><a id="8872" class="Symbol">}}</a>
        <a id="8883" class="Symbol">{{</a><a id="8885" href="simple_essence.html#8885" class="Bound">_</a> <a id="8887" class="Symbol">:</a> <a id="8889" href="simple_essence.html#7810" class="Record">VectorSpace</a> <a id="8901" href="simple_essence.html#8818" class="Bound">A</a><a id="8902" class="Symbol">}}</a>
        <a id="8913" class="Comment">-------------------------------------</a>
      <a id="8957" class="Symbol">→</a> <a id="8959" href="simple_essence.html#7064" class="Record">LinMap</a> <a id="8966" href="simple_essence.html#8818" class="Bound">A</a> <a id="8968" href="simple_essence.html#6138" class="Datatype">§</a> <a id="8970" class="Symbol">→</a> <a id="8972" href="simple_essence.html#8818" class="Bound">A</a>
<a id="8974" href="simple_essence.html#8809" class="Function">a⊸§→a</a> <a id="8980" class="Symbol">=</a> <a id="8982" class="Symbol">λ</a> <a id="8984" class="Symbol">{</a> <a id="8986" href="simple_essence.html#8986" class="Bound">lm</a> <a id="8989" class="Symbol">→</a> <a id="8991" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8997" class="Symbol">(λ</a> <a id="9000" href="simple_essence.html#9000" class="Bound">acc</a> <a id="9004" href="simple_essence.html#9004" class="Bound">v</a> <a id="9006" class="Symbol">→</a> <a id="9008" href="simple_essence.html#9000" class="Bound">acc</a> <a id="9012" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="9014" class="Symbol">(</a><a id="9015" href="simple_essence.html#7258" class="Field">LinMap.f</a> <a id="9024" href="simple_essence.html#8986" class="Bound">lm</a> <a id="9027" href="simple_essence.html#9004" class="Bound">v</a><a id="9028" class="Symbol">)</a> <a id="9030" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="9032" href="simple_essence.html#9004" class="Bound">v</a><a id="9033" class="Symbol">)</a> <a id="9035" href="simple_essence.html#6291" class="Field">id⊕</a> <a id="9039" href="simple_essence.html#8030" class="Field">basisSet</a> <a id="9048" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="9051" href="simple_essence.html#9051" class="Function">a⊸§←a</a> <a id="9057" class="Symbol">:</a> <a id="9059" class="Symbol">{</a><a id="9060" href="simple_essence.html#9060" class="Bound">A</a> <a id="9062" class="Symbol">:</a> <a id="9064" class="PrimitiveType">Set</a> <a id="9068" href="simple_essence.html#5524" class="Bound">a</a><a id="9069" class="Symbol">}</a>
        <a id="9079" class="Symbol">{{</a><a id="9081" href="simple_essence.html#9081" class="Bound">_</a> <a id="9083" class="Symbol">:</a> <a id="9085" href="simple_essence.html#6178" class="Record">Additive</a> <a id="9094" href="simple_essence.html#9060" class="Bound">A</a><a id="9095" class="Symbol">}}</a> <a id="9098" class="Symbol">{{</a><a id="9100" href="simple_essence.html#9100" class="Bound">_</a> <a id="9102" class="Symbol">:</a> <a id="9104" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="9113" href="simple_essence.html#9060" class="Bound">A</a><a id="9114" class="Symbol">}}</a>
        <a id="9125" class="Symbol">{{</a><a id="9127" href="simple_essence.html#9127" class="Bound">_</a> <a id="9129" class="Symbol">:</a> <a id="9131" href="simple_essence.html#7810" class="Record">VectorSpace</a> <a id="9143" href="simple_essence.html#9060" class="Bound">A</a><a id="9144" class="Symbol">}}</a>
        <a id="9155" class="Comment">-------------------------------------</a>
      <a id="9199" class="Symbol">→</a> <a id="9201" href="simple_essence.html#9060" class="Bound">A</a> <a id="9203" class="Symbol">→</a> <a id="9205" href="simple_essence.html#7064" class="Record">LinMap</a> <a id="9212" href="simple_essence.html#9060" class="Bound">A</a> <a id="9214" href="simple_essence.html#6138" class="Datatype">§</a>
<a id="9216" href="simple_essence.html#9051" class="Function">a⊸§←a</a> <a id="9222" class="Symbol">=</a> <a id="9224" class="Symbol">λ</a> <a id="9226" class="Symbol">{</a> <a id="9228" href="simple_essence.html#9228" class="Bound">a</a> <a id="9230" class="Symbol">→</a> <a id="9232" href="simple_essence.html#7241" class="InductiveConstructor">mkLM</a> <a id="9237" class="Symbol">(</a><a id="9238" href="simple_essence.html#9228" class="Bound">a</a> <a id="9240" href="simple_essence.html#8055" class="Field Operator">·_</a><a id="9242" class="Symbol">)</a> <a id="9244" href="simple_essence.html#8133" class="Field">·-distrib-⊕</a> <a id="9256" href="simple_essence.html#8265" class="Field">·-comm-⊛</a> <a id="9265" class="Symbol">}</a>

<a id="9268" class="Comment">-- Danger, Will Robinson!</a>
<a id="9294" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9306" href="simple_essence.html#9306" class="Postulate">x·z≡y·z→x≡y</a> <a id="9318" class="Symbol">:</a> <a id="9320" class="Symbol">{</a><a id="9321" href="simple_essence.html#9321" class="Bound">A</a> <a id="9323" class="Symbol">:</a> <a id="9325" class="PrimitiveType">Set</a> <a id="9329" href="simple_essence.html#5524" class="Bound">a</a><a id="9330" class="Symbol">}</a>
                <a id="9348" class="Symbol">{{</a><a id="9350" href="simple_essence.html#9350" class="Bound">_</a> <a id="9352" class="Symbol">:</a> <a id="9354" href="simple_essence.html#6178" class="Record">Additive</a> <a id="9363" href="simple_essence.html#9321" class="Bound">A</a><a id="9364" class="Symbol">}}</a> <a id="9367" class="Symbol">{{</a><a id="9369" href="simple_essence.html#9369" class="Bound">_</a> <a id="9371" class="Symbol">:</a> <a id="9373" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="9382" href="simple_essence.html#9321" class="Bound">A</a><a id="9383" class="Symbol">}}</a> <a id="9386" class="Symbol">{{</a><a id="9388" href="simple_essence.html#9388" class="Bound">_</a> <a id="9390" class="Symbol">:</a> <a id="9392" href="simple_essence.html#7810" class="Record">VectorSpace</a> <a id="9404" href="simple_essence.html#9321" class="Bound">A</a><a id="9405" class="Symbol">}}</a>
                <a id="9424" class="Symbol">{</a><a id="9425" href="simple_essence.html#9425" class="Bound">x</a> <a id="9427" href="simple_essence.html#9427" class="Bound">y</a> <a id="9429" class="Symbol">:</a> <a id="9431" href="simple_essence.html#9321" class="Bound">A</a><a id="9432" class="Symbol">}</a>
              <a id="9448" class="Symbol">→</a> <a id="9450" class="Symbol">(∀</a> <a id="9453" class="Symbol">{</a><a id="9454" href="simple_essence.html#9454" class="Bound">z</a> <a id="9456" class="Symbol">:</a> <a id="9458" href="simple_essence.html#9321" class="Bound">A</a><a id="9459" class="Symbol">}</a> <a id="9461" class="Symbol">→</a> <a id="9463" href="simple_essence.html#9425" class="Bound">x</a> <a id="9465" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="9467" href="simple_essence.html#9454" class="Bound">z</a> <a id="9469" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9471" href="simple_essence.html#9427" class="Bound">y</a> <a id="9473" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="9475" href="simple_essence.html#9454" class="Bound">z</a><a id="9476" class="Symbol">)</a>
                <a id="9494" class="Comment">-----------------------------------------------------------</a>
              <a id="9568" class="Symbol">→</a> <a id="9570" href="simple_essence.html#9425" class="Bound">x</a> <a id="9572" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9574" href="simple_essence.html#9427" class="Bound">y</a>
<a id="9576" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9636" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9703" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9734" href="simple_essence.html#9734" class="Function">a⊸§↔a</a> <a id="9740" class="Symbol">:</a> <a id="9742" class="Symbol">{</a><a id="9743" href="simple_essence.html#9743" class="Bound">A</a> <a id="9745" class="Symbol">:</a> <a id="9747" class="PrimitiveType">Set</a> <a id="9751" href="simple_essence.html#5524" class="Bound">a</a><a id="9752" class="Symbol">}</a>
        <a id="9762" class="Symbol">{{</a><a id="9764" href="simple_essence.html#9764" class="Bound">_</a> <a id="9766" class="Symbol">:</a> <a id="9768" href="simple_essence.html#6178" class="Record">Additive</a> <a id="9777" href="simple_essence.html#9743" class="Bound">A</a><a id="9778" class="Symbol">}}</a> <a id="9781" class="Symbol">{{</a><a id="9783" href="simple_essence.html#9783" class="Bound">_</a> <a id="9785" class="Symbol">:</a> <a id="9787" href="simple_essence.html#6792" class="Record">Scalable</a> <a id="9796" href="simple_essence.html#9743" class="Bound">A</a><a id="9797" class="Symbol">}}</a>
        <a id="9808" class="Symbol">{{</a><a id="9810" href="simple_essence.html#9810" class="Bound">_</a> <a id="9812" class="Symbol">:</a> <a id="9814" href="simple_essence.html#7810" class="Record">VectorSpace</a> <a id="9826" href="simple_essence.html#9743" class="Bound">A</a><a id="9827" class="Symbol">}}</a>
        <a id="9838" class="Comment">-------------------------------------</a>
      <a id="9882" class="Symbol">→</a> <a id="9884" class="Symbol">(</a><a id="9885" href="simple_essence.html#7064" class="Record">LinMap</a> <a id="9892" href="simple_essence.html#9743" class="Bound">A</a> <a id="9894" href="simple_essence.html#6138" class="Datatype">§</a><a id="9895" class="Symbol">)</a> <a id="9897" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9899" href="simple_essence.html#9743" class="Bound">A</a>
<a id="9901" href="simple_essence.html#9734" class="Function">a⊸§↔a</a> <a id="9907" class="Symbol">{</a><a id="9908" href="simple_essence.html#9908" class="Bound">A</a><a id="9909" class="Symbol">}</a> <a id="9911" class="Symbol">=</a>
  <a id="9915" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9919" class="Symbol">{</a><a id="9920" class="Argument">f</a> <a id="9922" class="Symbol">=</a> <a id="9924" href="simple_essence.html#8809" class="Function">a⊸§→a</a><a id="9929" class="Symbol">}</a> <a id="9931" class="Symbol">{</a><a id="9932" class="Argument">f⁻¹</a> <a id="9936" class="Symbol">=</a> <a id="9938" href="simple_essence.html#9051" class="Function">a⊸§←a</a><a id="9943" class="Symbol">}</a>
      <a id="9951" class="Symbol">(</a> <a id="9953" class="Symbol">(λ</a> <a id="9956" class="Symbol">{</a><a id="9957" href="simple_essence.html#9957" class="Bound">x</a> <a id="9959" class="Symbol">→</a> <a id="9961" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="9985" href="simple_essence.html#8809" class="Function">a⊸§→a</a> <a id="9991" class="Symbol">(</a><a id="9992" href="simple_essence.html#9051" class="Function">a⊸§←a</a> <a id="9998" href="simple_essence.html#9957" class="Bound">x</a><a id="9999" class="Symbol">)</a>
                <a id="10017" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10039" href="simple_essence.html#8809" class="Function">a⊸§→a</a> <a id="10045" class="Symbol">(</a><a id="10046" href="simple_essence.html#7241" class="InductiveConstructor">mkLM</a> <a id="10051" class="Symbol">(</a><a id="10052" href="simple_essence.html#9957" class="Bound">x</a> <a id="10054" href="simple_essence.html#8055" class="Field Operator">·_</a><a id="10056" class="Symbol">)</a> <a id="10058" href="simple_essence.html#8133" class="Field">·-distrib-⊕</a> <a id="10070" href="simple_essence.html#8265" class="Field">·-comm-⊛</a><a id="10078" class="Symbol">)</a>
                <a id="10096" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10118" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10124" class="Symbol">(λ</a> <a id="10127" href="simple_essence.html#10127" class="Bound">acc</a> <a id="10131" href="simple_essence.html#10131" class="Bound">v</a> <a id="10133" class="Symbol">→</a> <a id="10135" href="simple_essence.html#10127" class="Bound">acc</a> <a id="10139" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="10141" class="Symbol">(</a><a id="10142" href="simple_essence.html#9957" class="Bound">x</a> <a id="10144" href="simple_essence.html#8055" class="Field Operator">·</a> <a id="10146" href="simple_essence.html#10131" class="Bound">v</a><a id="10147" class="Symbol">)</a> <a id="10149" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="10151" href="simple_essence.html#10131" class="Bound">v</a><a id="10152" class="Symbol">)</a> <a id="10154" href="simple_essence.html#6291" class="Field">id⊕</a> <a id="10158" href="simple_essence.html#8030" class="Field">basisSet</a>
                <a id="10183" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10186" href="simple_essence.html#9306" class="Postulate">x·z≡y·z→x≡y</a> <a id="10198" class="Symbol">(</a><a id="10199" href="simple_essence.html#8533" class="Field">orthonormal</a> <a id="10211" class="Symbol">{</a><a id="10212" class="Argument">f</a> <a id="10214" class="Symbol">=</a> <a id="10216" class="Symbol">(</a><a id="10217" href="simple_essence.html#9957" class="Bound">x</a> <a id="10219" href="simple_essence.html#8055" class="Field Operator">·_</a><a id="10221" class="Symbol">)})</a> <a id="10225" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10245" href="simple_essence.html#9957" class="Bound">x</a>
                <a id="10263" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10264" class="Symbol">})</a>
      <a id="10273" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10275" class="Symbol">λ</a> <a id="10277" class="Symbol">{</a><a id="10278" href="simple_essence.html#10278" class="Bound">lm</a> <a id="10281" class="Symbol">→</a> <a id="10283" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10307" href="simple_essence.html#9051" class="Function">a⊸§←a</a> <a id="10313" class="Symbol">(</a><a id="10314" href="simple_essence.html#8809" class="Function">a⊸§→a</a> <a id="10320" href="simple_essence.html#10278" class="Bound">lm</a><a id="10322" class="Symbol">)</a>
                <a id="10340" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10362" href="simple_essence.html#9051" class="Function">a⊸§←a</a> <a id="10368" class="Symbol">(</a><a id="10369" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10375" class="Symbol">(λ</a> <a id="10378" href="simple_essence.html#10378" class="Bound">acc</a> <a id="10382" href="simple_essence.html#10382" class="Bound">v</a> <a id="10384" class="Symbol">→</a> <a id="10386" href="simple_essence.html#10378" class="Bound">acc</a> <a id="10390" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="10392" class="Symbol">(</a><a id="10393" href="simple_essence.html#7258" class="Field">LinMap.f</a> <a id="10402" href="simple_essence.html#10278" class="Bound">lm</a> <a id="10405" href="simple_essence.html#10382" class="Bound">v</a><a id="10406" class="Symbol">)</a> <a id="10408" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="10410" href="simple_essence.html#10382" class="Bound">v</a><a id="10411" class="Symbol">)</a> <a id="10413" href="simple_essence.html#6291" class="Field">id⊕</a> <a id="10417" href="simple_essence.html#8030" class="Field">basisSet</a><a id="10425" class="Symbol">)</a>
                <a id="10443" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10465" href="simple_essence.html#7241" class="InductiveConstructor">mkLM</a> <a id="10470" class="Symbol">((</a><a id="10472" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10478" class="Symbol">(λ</a> <a id="10481" href="simple_essence.html#10481" class="Bound">acc</a> <a id="10485" href="simple_essence.html#10485" class="Bound">v</a> <a id="10487" class="Symbol">→</a> <a id="10489" href="simple_essence.html#10481" class="Bound">acc</a> <a id="10493" href="simple_essence.html#6304" class="Field Operator">⊕</a> <a id="10495" class="Symbol">(</a><a id="10496" href="simple_essence.html#7258" class="Field">LinMap.f</a> <a id="10505" href="simple_essence.html#10278" class="Bound">lm</a> <a id="10508" href="simple_essence.html#10485" class="Bound">v</a><a id="10509" class="Symbol">)</a> <a id="10511" href="simple_essence.html#6905" class="Field Operator">⊛</a> <a id="10513" href="simple_essence.html#10485" class="Bound">v</a><a id="10514" class="Symbol">)</a> <a id="10516" href="simple_essence.html#6291" class="Field">id⊕</a> <a id="10520" href="simple_essence.html#8030" class="Field">basisSet</a><a id="10528" class="Symbol">)</a><a id="10529" href="simple_essence.html#8055" class="Field Operator">·_</a><a id="10531" class="Symbol">)</a>
                       <a id="10556" href="simple_essence.html#8133" class="Field">·-distrib-⊕</a> <a id="10568" href="simple_essence.html#8265" class="Field">·-comm-⊛</a>
                <a id="10593" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10596" href="simple_essence.html#7576" class="Postulate">⊸≡</a> <a id="10599" class="Symbol">(</a> <a id="10601" href="simple_essence.html#6057" class="Postulate">extensionality</a>
                          <a id="10642" class="Symbol">(</a> <a id="10644" class="Symbol">λ</a> <a id="10646" href="simple_essence.html#10646" class="Bound">x</a> <a id="10648" class="Symbol">→</a> <a id="10650" href="simple_essence.html#8533" class="Field">orthonormal</a> <a id="10662" class="Symbol">{</a><a id="10663" class="Argument">f</a> <a id="10665" class="Symbol">=</a> <a id="10667" href="simple_essence.html#7258" class="Field">LinMap.f</a> <a id="10676" href="simple_essence.html#10278" class="Bound">lm</a><a id="10678" class="Symbol">}</a> <a id="10680" class="Symbol">{</a><a id="10681" class="Argument">x</a> <a id="10683" class="Symbol">=</a> <a id="10685" href="simple_essence.html#10646" class="Bound">x</a><a id="10686" class="Symbol">}</a> <a id="10688" class="Symbol">)</a>
                      <a id="10712" class="Symbol">)</a>
                 <a id="10731" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10751" href="simple_essence.html#10278" class="Bound">lm</a>
                <a id="10770" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10771" class="Symbol">}</a>
      <a id="10779" class="Symbol">)</a>

<a id="10782" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10865" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10927" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="11021" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="11084" class="Comment">--</a>
<a id="11087" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="11110" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="11159" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="11192" class="Comment">--         -------------------------------------</a>
<a id="11241" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11269" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>