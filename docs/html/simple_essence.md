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

> The internal representation of $Cont^{s}_{(⊸)} \, a \, b$ is $(b ⊸ s) → (a ⊸ s)$, which is isomorphic to $b → a$.

I thought for sure Conal meant to say:

> ... isomorphic to $a → b$.

since the continuation must "know" how to get from `a` to `b`, in order to offer the type signature it does.
(Can this be proven in Agda, perhaps by using a proof-by-contradiction approach?)

But, when I discussed this with Conal, he drew my attention to the paragraph immediately above, in which he points out:

> In particular, every linear map in $A ⊸ s$ has the form `dot u` for some `u :: A`,

And that, therefore, since $a ⊸ s$ is isomorphic to $a$,  $(b ⊸ s) → (a ⊸ s)$ is indeed isomorphic to $$b → a$$.

Well, that's very interesting, because now we've got something (the _continuation_) that is isomorphic to both $a → b$ and $b → a$.
And, because the isomorphism relation is _transitive_, that means: $a → b ≅ b → a$!
Of course, this only holds in the special case where both types $a$ and $b$ have linear maps to the underlying scalar field.
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

1. The $\oplus$ operator must take two arguments of the same type and combine them, returning a result also within the type.

1. Both types $A$ and $B$ _must_ have the $\oplus$ operator defined on them.

1. The $\otimes$ operator must take a scalar as its first argument and some type as its second, returning a result value within that type.

1. Both types $A$ and $B$ _must_ have the $\otimes$ operator defined on them.

We can codify all this in Agda fairly easily:

{% highlight agda linenos %}
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

    a⊸§≃a : ∀ {A : Set} {{_ : Additive A}} {{_ : Scalable A}}
            -------------------------------------------------
          → LinMap {A} {§} ≃ A
    a⊸§≃a = record
      { to   = λ { lm → ? }
      ; from = λ { a  → ? }
      ; from∘to = ?
      ; to∘from = ?
      }

Now, how to implement `to` and `from`?

If we required that `Additive` provide a _left identity_ for `⊕` then it would be enough to require that `A` be able to produce an iterable set of basis vectors.
In that case, `to` could be implemented, via the following:

    to = λ lm → foldl (λ acc v → acc ⊕ (lm.f v) ⊛ v) id-⊕ vs

Implementing `from` is fairly simple, but does require that `A` have an inner product.
In that case, we just build a `LinMap` record where `f` takes the dot product of its
input w/ `a`.

**Note:** My hunch is that I'm going to have to define some property of type `A` that relates the "inner product" to its "basis vectors", in order to tie all this together, but it's unclear to me what that property is, or needs to be.

## First Proof Attempt

Let's try adding the extra necessities identified above and attacking the proof.
I'll note any additional properties, record fields, etc. needed to complete the proof, via Agda comments, for subsequent discussion.

<pre class="Agda"><a id="5351" class="Keyword">module</a> <a id="5358" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5373" class="Symbol">{</a><a id="5374" href="simple_essence.html#5374" class="Bound">s</a> <a id="5376" href="simple_essence.html#5376" class="Bound">a</a> <a id="5378" href="simple_essence.html#5378" class="Bound">b</a><a id="5379" class="Symbol">}</a> <a id="5381" class="Keyword">where</a>

<a id="5388" class="Keyword">open</a> <a id="5393" class="Keyword">import</a> <a id="5400" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5419" class="Keyword">open</a> <a id="5424" class="Keyword">import</a> <a id="5431" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5466" class="Keyword">using</a> <a id="5472" class="Symbol">(</a><a id="5473" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5487" class="Symbol">)</a>
<a id="5489" class="Keyword">open</a> <a id="5494" class="Keyword">import</a> <a id="5501" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5512" class="Keyword">open</a> <a id="5517" class="Keyword">import</a> <a id="5524" href="Data.List.html" class="Module">Data.List</a>
<a id="5534" class="Keyword">open</a> <a id="5539" class="Keyword">import</a> <a id="5546" href="Function.html" class="Module">Function</a> <a id="5555" class="Keyword">using</a> <a id="5561" class="Symbol">(</a><a id="5562" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5565" class="Symbol">;</a> <a id="5567" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5570" class="Symbol">;</a> <a id="5572" href="Function.Base.html#615" class="Function">id</a><a id="5574" class="Symbol">)</a>
<a id="5576" class="Keyword">open</a> <a id="5581" class="Keyword">import</a> <a id="5588" href="Level.html" class="Module">Level</a> <a id="5594" class="Keyword">using</a> <a id="5600" class="Symbol">(</a><a id="5601" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5606" class="Symbol">;</a> <a id="5608" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5611" class="Symbol">)</a>

<a id="5614" class="Keyword">import</a> <a id="5621" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5659" class="Symbol">as</a> <a id="5662" class="Module">Eq</a>
<a id="5665" class="Keyword">open</a> <a id="5670" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5673" class="Keyword">using</a> <a id="5679" class="Symbol">(</a><a id="5680" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5683" class="Symbol">;</a> <a id="5685" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5689" class="Symbol">;</a> <a id="5691" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5696" class="Symbol">;</a> <a id="5698" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5701" class="Symbol">;</a> <a id="5703" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5707" class="Symbol">;</a> <a id="5709" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5714" class="Symbol">;</a> <a id="5716" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5724" class="Symbol">;</a> <a id="5726" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5731" class="Symbol">)</a>
<a id="5733" class="Keyword">open</a> <a id="5738" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5753" class="Keyword">using</a> <a id="5759" class="Symbol">(</a><a id="5760" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5766" class="Symbol">;</a> <a id="5768" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5773" class="Symbol">;</a> <a id="5775" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5781" class="Symbol">;</a> <a id="5783" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5785" class="Symbol">)</a>

<a id="5788" class="Keyword">postulate</a>
  <a id="5800" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="5875" href="simple_essence.html#5875" class="Postulate">id+</a> <a id="5879" class="Symbol">:</a> <a id="5881" class="Symbol">{</a><a id="5882" href="simple_essence.html#5882" class="Bound">x</a> <a id="5884" class="Symbol">:</a> <a id="5886" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="5891" class="Symbol">}</a> <a id="5893" class="Symbol">→</a> <a id="5895" class="Number">0.0</a> <a id="5899" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="5901" href="simple_essence.html#5882" class="Bound">x</a> <a id="5903" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5905" href="simple_essence.html#5882" class="Bound">x</a>
  <a id="extensionality"></a><a id="5909" href="simple_essence.html#5909" class="Postulate">extensionality</a> <a id="5924" class="Symbol">:</a> <a id="5926" class="Symbol">∀</a> <a id="5928" class="Symbol">{</a><a id="5929" href="simple_essence.html#5929" class="Bound">ℓ₁</a> <a id="5932" href="simple_essence.html#5932" class="Bound">ℓ₂</a><a id="5934" class="Symbol">}</a> <a id="5936" class="Symbol">→</a> <a id="5938" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="5953" href="simple_essence.html#5929" class="Bound">ℓ₁</a> <a id="5956" href="simple_essence.html#5932" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="5960" href="simple_essence.html#5960" class="Function">ℓ</a> <a id="5962" class="Symbol">:</a> <a id="5964" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="5970" href="simple_essence.html#5960" class="Function">ℓ</a> <a id="5972" class="Symbol">=</a> <a id="5974" href="simple_essence.html#5374" class="Bound">s</a> <a id="5976" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5978" href="simple_essence.html#5376" class="Bound">a</a> <a id="5980" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5982" href="simple_essence.html#5378" class="Bound">b</a>

<a id="5985" class="Keyword">data</a> <a id="§"></a><a id="5990" href="simple_essence.html#5990" class="Datatype">§</a> <a id="5992" class="Symbol">:</a> <a id="5994" class="PrimitiveType">Set</a> <a id="5998" href="simple_essence.html#5376" class="Bound">a</a> <a id="6000" class="Keyword">where</a>
  <a id="§.S"></a><a id="6008" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6010" class="Symbol">:</a> <a id="6012" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="6018" class="Symbol">→</a> <a id="6020" href="simple_essence.html#5990" class="Datatype">§</a>

<a id="6023" class="Keyword">record</a> <a id="Additive"></a><a id="6030" href="simple_essence.html#6030" class="Record">Additive</a> <a id="6039" class="Symbol">(</a><a id="6040" href="simple_essence.html#6040" class="Bound">A</a> <a id="6042" class="Symbol">:</a> <a id="6044" class="PrimitiveType">Set</a> <a id="6048" href="simple_essence.html#5376" class="Bound">a</a><a id="6049" class="Symbol">)</a> <a id="6051" class="Symbol">:</a> <a id="6053" class="PrimitiveType">Set</a> <a id="6057" href="simple_essence.html#5960" class="Function">ℓ</a> <a id="6059" class="Keyword">where</a>
  <a id="6067" class="Keyword">infixl</a> <a id="6074" class="Number">6</a> <a id="6076" href="simple_essence.html#6156" class="Field Operator">_⊕_</a>  <a id="6081" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6133" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6143" href="simple_essence.html#6143" class="Field">id⊕</a>  <a id="6148" class="Symbol">:</a> <a id="6150" href="simple_essence.html#6040" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6156" href="simple_essence.html#6156" class="Field Operator">_⊕_</a>  <a id="6161" class="Symbol">:</a> <a id="6163" href="simple_essence.html#6040" class="Bound">A</a> <a id="6165" class="Symbol">→</a> <a id="6167" href="simple_essence.html#6040" class="Bound">A</a> <a id="6169" class="Symbol">→</a> <a id="6171" href="simple_essence.html#6040" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6177" href="simple_essence.html#6177" class="Field">id-⊕</a> <a id="6182" class="Symbol">:</a> <a id="6184" class="Symbol">(</a><a id="6185" href="simple_essence.html#6185" class="Bound">a</a> <a id="6187" class="Symbol">:</a> <a id="6189" href="simple_essence.html#6040" class="Bound">A</a><a id="6190" class="Symbol">)</a>
           <a id="6203" class="Comment">-----------</a>
         <a id="6224" class="Symbol">→</a> <a id="6226" href="simple_essence.html#6143" class="Field">id⊕</a> <a id="6230" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="6232" href="simple_essence.html#6185" class="Bound">a</a> <a id="6234" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6236" href="simple_essence.html#6185" class="Bound">a</a>
    <a id="6242" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6295" class="Keyword">open</a> <a id="6300" href="simple_essence.html#6030" class="Module">Additive</a> <a id="6309" class="Symbol">{{</a> <a id="6312" class="Symbol">...</a> <a id="6316" class="Symbol">}}</a>
<a id="6319" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6330" href="simple_essence.html#6330" class="Function">AdditiveScalar</a> <a id="6345" class="Symbol">:</a> <a id="6347" href="simple_essence.html#6030" class="Record">Additive</a> <a id="6356" href="simple_essence.html#5990" class="Datatype">§</a>
  <a id="6360" href="simple_essence.html#6330" class="Function">AdditiveScalar</a> <a id="6375" class="Symbol">=</a> <a id="6377" class="Keyword">record</a>
    <a id="6388" class="Symbol">{</a> <a id="6390" href="simple_essence.html#6143" class="Field">id⊕</a>  <a id="6395" class="Symbol">=</a> <a id="6397" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6399" class="Number">0.0</a>
    <a id="6407" class="Symbol">;</a> <a id="6409" href="simple_essence.html#6156" class="Field Operator">_⊕_</a>  <a id="6414" class="Symbol">=</a> <a id="6416" class="Symbol">λ</a> <a id="6418" class="Symbol">{(</a><a id="6420" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6422" href="simple_essence.html#6422" class="Bound">x</a><a id="6423" class="Symbol">)</a> <a id="6425" class="Symbol">(</a><a id="6426" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6428" href="simple_essence.html#6428" class="Bound">y</a><a id="6429" class="Symbol">)</a> <a id="6431" class="Symbol">→</a> <a id="6433" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6435" class="Symbol">(</a><a id="6436" href="simple_essence.html#6422" class="Bound">x</a> <a id="6438" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6440" href="simple_essence.html#6428" class="Bound">y</a><a id="6441" class="Symbol">)}</a>
    <a id="6448" class="Symbol">;</a> <a id="6450" href="simple_essence.html#6177" class="Field">id-⊕</a> <a id="6455" class="Symbol">=</a> <a id="6457" class="Symbol">λ</a> <a id="6459" class="Symbol">{</a> <a id="6461" class="Symbol">(</a><a id="6462" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6464" href="simple_essence.html#6464" class="Bound">x</a><a id="6465" class="Symbol">)</a> <a id="6467" class="Symbol">→</a> <a id="6469" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6502" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6504" class="Symbol">(</a><a id="6505" class="Number">0.0</a> <a id="6509" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6511" href="simple_essence.html#6464" class="Bound">x</a><a id="6512" class="Symbol">)</a>
                         <a id="6539" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6542" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6547" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6549" href="simple_essence.html#5875" class="Postulate">id+</a> <a id="6553" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6582" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6584" href="simple_essence.html#6464" class="Bound">x</a>
                         <a id="6611" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6628" class="Symbol">}</a>
    <a id="6634" class="Symbol">}</a>

<a id="6637" class="Keyword">record</a> <a id="Scalable"></a><a id="6644" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="6653" class="Symbol">(</a><a id="6654" href="simple_essence.html#6654" class="Bound">A</a> <a id="6656" class="Symbol">:</a> <a id="6658" class="PrimitiveType">Set</a> <a id="6662" href="simple_essence.html#5376" class="Bound">a</a><a id="6663" class="Symbol">)</a> <a id="6665" class="Symbol">:</a> <a id="6667" class="PrimitiveType">Set</a> <a id="6671" href="simple_essence.html#5960" class="Function">ℓ</a> <a id="6673" class="Keyword">where</a>
  <a id="6681" class="Keyword">infixl</a> <a id="6688" class="Number">7</a> <a id="6690" href="simple_essence.html#6757" class="Field Operator">_⊛_</a>  <a id="6695" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6747" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6757" href="simple_essence.html#6757" class="Field Operator">_⊛_</a> <a id="6761" class="Symbol">:</a> <a id="6763" href="simple_essence.html#5990" class="Datatype">§</a> <a id="6765" class="Symbol">→</a> <a id="6767" href="simple_essence.html#6654" class="Bound">A</a> <a id="6769" class="Symbol">→</a> <a id="6771" href="simple_essence.html#6654" class="Bound">A</a>
<a id="6773" class="Keyword">open</a> <a id="6778" href="simple_essence.html#6644" class="Module">Scalable</a> <a id="6787" class="Symbol">{{</a> <a id="6790" class="Symbol">...</a> <a id="6794" class="Symbol">}}</a>
<a id="6797" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="6808" href="simple_essence.html#6808" class="Function">ScalableScalar</a> <a id="6823" class="Symbol">:</a> <a id="6825" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="6834" href="simple_essence.html#5990" class="Datatype">§</a>
  <a id="6838" href="simple_essence.html#6808" class="Function">ScalableScalar</a> <a id="6853" class="Symbol">=</a> <a id="6855" class="Keyword">record</a>
    <a id="6866" class="Symbol">{</a> <a id="6868" href="simple_essence.html#6757" class="Field Operator">_⊛_</a> <a id="6872" class="Symbol">=</a> <a id="6874" class="Symbol">λ</a> <a id="6876" class="Symbol">{(</a><a id="6878" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6880" href="simple_essence.html#6880" class="Bound">x</a><a id="6881" class="Symbol">)</a> <a id="6883" class="Symbol">(</a><a id="6884" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6886" href="simple_essence.html#6886" class="Bound">y</a><a id="6887" class="Symbol">)</a> <a id="6889" class="Symbol">→</a> <a id="6891" href="simple_essence.html#6008" class="InductiveConstructor">S</a> <a id="6893" class="Symbol">(</a><a id="6894" href="simple_essence.html#6880" class="Bound">x</a> <a id="6896" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="6898" href="simple_essence.html#6886" class="Bound">y</a><a id="6899" class="Symbol">)}</a>
    <a id="6906" class="Symbol">}</a>

<a id="6909" class="Keyword">record</a> <a id="LinMap"></a><a id="6916" href="simple_essence.html#6916" class="Record">LinMap</a> <a id="6923" class="Symbol">(</a><a id="6924" href="simple_essence.html#6924" class="Bound">A</a> <a id="6926" class="Symbol">:</a> <a id="6928" class="PrimitiveType">Set</a> <a id="6932" href="simple_essence.html#5376" class="Bound">a</a><a id="6933" class="Symbol">)</a> <a id="6935" class="Symbol">(</a><a id="6936" href="simple_essence.html#6936" class="Bound">B</a> <a id="6938" class="Symbol">:</a> <a id="6940" class="PrimitiveType">Set</a> <a id="6944" href="simple_essence.html#5376" class="Bound">a</a><a id="6945" class="Symbol">)</a>
              <a id="6961" class="Symbol">{{</a><a id="6963" href="simple_essence.html#6963" class="Bound">_</a> <a id="6965" class="Symbol">:</a> <a id="6967" href="simple_essence.html#6030" class="Record">Additive</a> <a id="6976" href="simple_essence.html#6924" class="Bound">A</a><a id="6977" class="Symbol">}}</a> <a id="6980" class="Symbol">{{</a><a id="6982" href="simple_essence.html#6982" class="Bound">_</a> <a id="6984" class="Symbol">:</a> <a id="6986" href="simple_essence.html#6030" class="Record">Additive</a> <a id="6995" href="simple_essence.html#6936" class="Bound">B</a><a id="6996" class="Symbol">}}</a>
              <a id="7013" class="Symbol">{{</a><a id="7015" href="simple_essence.html#7015" class="Bound">_</a> <a id="7017" class="Symbol">:</a> <a id="7019" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="7028" href="simple_essence.html#6924" class="Bound">A</a><a id="7029" class="Symbol">}}</a> <a id="7032" class="Symbol">{{</a><a id="7034" href="simple_essence.html#7034" class="Bound">_</a> <a id="7036" class="Symbol">:</a> <a id="7038" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="7047" href="simple_essence.html#6936" class="Bound">B</a><a id="7048" class="Symbol">}}</a>
              <a id="7065" class="Symbol">:</a> <a id="7067" class="PrimitiveType">Set</a> <a id="7071" href="simple_essence.html#5960" class="Function">ℓ</a> <a id="7073" class="Keyword">where</a>
  <a id="7081" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7093" href="simple_essence.html#7093" class="InductiveConstructor">mkLM</a>
  <a id="7100" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7110" href="simple_essence.html#7110" class="Field">f</a>      <a id="7117" class="Symbol">:</a> <a id="7119" href="simple_essence.html#6924" class="Bound">A</a> <a id="7121" class="Symbol">→</a> <a id="7123" href="simple_essence.html#6936" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7130" href="simple_essence.html#7130" class="Field">adds</a>   <a id="7137" class="Symbol">:</a> <a id="7139" class="Symbol">∀</a> <a id="7141" class="Symbol">{</a><a id="7142" href="simple_essence.html#7142" class="Bound">a</a> <a id="7144" href="simple_essence.html#7144" class="Bound">b</a> <a id="7146" class="Symbol">:</a> <a id="7148" href="simple_essence.html#6924" class="Bound">A</a><a id="7149" class="Symbol">}</a>
             <a id="7164" class="Comment">---------------------</a>
           <a id="7197" class="Symbol">→</a> <a id="7199" href="simple_essence.html#7110" class="Field">f</a> <a id="7201" class="Symbol">(</a><a id="7202" href="simple_essence.html#7142" class="Bound">a</a> <a id="7204" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="7206" href="simple_essence.html#7144" class="Bound">b</a><a id="7207" class="Symbol">)</a> <a id="7209" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7211" href="simple_essence.html#7110" class="Field">f</a> <a id="7213" href="simple_essence.html#7142" class="Bound">a</a> <a id="7215" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="7217" href="simple_essence.html#7110" class="Field">f</a> <a id="7219" href="simple_essence.html#7144" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7226" href="simple_essence.html#7226" class="Field">scales</a> <a id="7233" class="Symbol">:</a> <a id="7235" class="Symbol">∀</a> <a id="7237" class="Symbol">{</a><a id="7238" href="simple_essence.html#7238" class="Bound">s</a> <a id="7240" class="Symbol">:</a> <a id="7242" href="simple_essence.html#5990" class="Datatype">§</a><a id="7243" class="Symbol">}</a> <a id="7245" class="Symbol">{</a><a id="7246" href="simple_essence.html#7246" class="Bound">a</a> <a id="7248" class="Symbol">:</a> <a id="7250" href="simple_essence.html#6924" class="Bound">A</a><a id="7251" class="Symbol">}</a>
             <a id="7266" class="Comment">-------------------</a>
           <a id="7297" class="Symbol">→</a> <a id="7299" href="simple_essence.html#7110" class="Field">f</a> <a id="7301" class="Symbol">(</a><a id="7302" href="simple_essence.html#7238" class="Bound">s</a> <a id="7304" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="7306" href="simple_essence.html#7246" class="Bound">a</a><a id="7307" class="Symbol">)</a> <a id="7309" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7311" href="simple_essence.html#7238" class="Bound">s</a> <a id="7313" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="7315" href="simple_essence.html#7110" class="Field">f</a> <a id="7317" href="simple_essence.html#7246" class="Bound">a</a>
<a id="7319" class="Keyword">open</a> <a id="7324" href="simple_essence.html#6916" class="Module">LinMap</a> <a id="7331" class="Symbol">{{</a> <a id="7334" class="Symbol">...</a> <a id="7338" class="Symbol">}}</a>

<a id="7342" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7368" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7416" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7428" href="simple_essence.html#7428" class="Postulate">⊸≡</a> <a id="7431" class="Symbol">:</a> <a id="7433" class="Symbol">{</a><a id="7434" href="simple_essence.html#7434" class="Bound">A</a> <a id="7436" href="simple_essence.html#7436" class="Bound">B</a> <a id="7438" class="Symbol">:</a> <a id="7440" class="PrimitiveType">Set</a> <a id="7444" href="simple_essence.html#5376" class="Bound">a</a><a id="7445" class="Symbol">}</a>
       <a id="7454" class="Symbol">{{</a><a id="7456" href="simple_essence.html#7456" class="Bound">_</a> <a id="7458" class="Symbol">:</a> <a id="7460" href="simple_essence.html#6030" class="Record">Additive</a> <a id="7469" href="simple_essence.html#7434" class="Bound">A</a><a id="7470" class="Symbol">}}</a> <a id="7473" class="Symbol">{{</a><a id="7475" href="simple_essence.html#7475" class="Bound">_</a> <a id="7477" class="Symbol">:</a> <a id="7479" href="simple_essence.html#6030" class="Record">Additive</a> <a id="7488" href="simple_essence.html#7436" class="Bound">B</a><a id="7489" class="Symbol">}}</a>
       <a id="7499" class="Symbol">{{</a><a id="7501" href="simple_essence.html#7501" class="Bound">_</a> <a id="7503" class="Symbol">:</a> <a id="7505" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="7514" href="simple_essence.html#7434" class="Bound">A</a><a id="7515" class="Symbol">}}</a> <a id="7518" class="Symbol">{{</a><a id="7520" href="simple_essence.html#7520" class="Bound">_</a> <a id="7522" class="Symbol">:</a> <a id="7524" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="7533" href="simple_essence.html#7436" class="Bound">B</a><a id="7534" class="Symbol">}}</a>
       <a id="7544" class="Symbol">{</a><a id="7545" href="simple_essence.html#7545" class="Bound">lm₁</a> <a id="7549" href="simple_essence.html#7549" class="Bound">lm₂</a> <a id="7553" class="Symbol">:</a> <a id="7555" href="simple_essence.html#6916" class="Record">LinMap</a> <a id="7562" href="simple_essence.html#7434" class="Bound">A</a> <a id="7564" href="simple_essence.html#7436" class="Bound">B</a><a id="7565" class="Symbol">}</a>
     <a id="7572" class="Symbol">→</a> <a id="7574" href="simple_essence.html#7110" class="Field">LinMap.f</a> <a id="7583" href="simple_essence.html#7545" class="Bound">lm₁</a> <a id="7587" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7589" href="simple_essence.html#7110" class="Field">LinMap.f</a> <a id="7598" href="simple_essence.html#7549" class="Bound">lm₂</a>
       <a id="7609" class="Comment">---------------------------</a>
     <a id="7642" class="Symbol">→</a> <a id="7644" href="simple_essence.html#7545" class="Bound">lm₁</a> <a id="7648" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7650" href="simple_essence.html#7549" class="Bound">lm₂</a>

<a id="7655" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7662" href="simple_essence.html#7662" class="Record">VectorSpace</a> <a id="7674" class="Symbol">(</a><a id="7675" href="simple_essence.html#7675" class="Bound">A</a> <a id="7677" class="Symbol">:</a> <a id="7679" class="PrimitiveType">Set</a> <a id="7683" href="simple_essence.html#5376" class="Bound">a</a><a id="7684" class="Symbol">)</a>
                   <a id="7705" class="Symbol">{{</a><a id="7707" href="simple_essence.html#7707" class="Bound">_</a> <a id="7709" class="Symbol">:</a> <a id="7711" href="simple_essence.html#6030" class="Record">Additive</a> <a id="7720" href="simple_essence.html#7675" class="Bound">A</a><a id="7721" class="Symbol">}}</a> <a id="7724" class="Symbol">{{</a><a id="7726" href="simple_essence.html#7726" class="Bound">_</a> <a id="7728" class="Symbol">:</a> <a id="7730" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="7739" href="simple_essence.html#7675" class="Bound">A</a><a id="7740" class="Symbol">}}</a>
                   <a id="7762" class="Symbol">:</a> <a id="7764" class="PrimitiveType">Set</a> <a id="7768" href="simple_essence.html#5960" class="Function">ℓ</a> <a id="7770" class="Keyword">where</a>
  <a id="7778" class="Keyword">field</a>
    <a id="7788" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="7882" href="simple_essence.html#7882" class="Field">basisSet</a>    <a id="7894" class="Symbol">:</a> <a id="7896" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="7901" href="simple_essence.html#7675" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="7907" href="simple_essence.html#7907" class="Field Operator">_·_</a>         <a id="7919" class="Symbol">:</a> <a id="7921" href="simple_essence.html#7675" class="Bound">A</a> <a id="7923" class="Symbol">→</a> <a id="7925" href="simple_essence.html#7675" class="Bound">A</a> <a id="7927" class="Symbol">→</a> <a id="7929" href="simple_essence.html#5990" class="Datatype">§</a>
    <a id="7935" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="7985" href="simple_essence.html#7985" class="Field">·-distrib-⊕</a> <a id="7997" class="Symbol">:</a> <a id="7999" class="Symbol">∀</a> <a id="8001" class="Symbol">{</a><a id="8002" href="simple_essence.html#8002" class="Bound">a</a> <a id="8004" href="simple_essence.html#8004" class="Bound">b</a> <a id="8006" href="simple_essence.html#8006" class="Bound">c</a> <a id="8008" class="Symbol">:</a> <a id="8010" href="simple_essence.html#7675" class="Bound">A</a><a id="8011" class="Symbol">}</a>
                  <a id="8031" class="Comment">-------------------------------</a>
                <a id="8079" class="Symbol">→</a> <a id="8081" href="simple_essence.html#8002" class="Bound">a</a> <a id="8083" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="8085" class="Symbol">(</a><a id="8086" href="simple_essence.html#8004" class="Bound">b</a> <a id="8088" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="8090" href="simple_essence.html#8006" class="Bound">c</a><a id="8091" class="Symbol">)</a> <a id="8093" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8095" class="Symbol">(</a><a id="8096" href="simple_essence.html#8002" class="Bound">a</a> <a id="8098" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="8100" href="simple_essence.html#8004" class="Bound">b</a><a id="8101" class="Symbol">)</a> <a id="8103" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="8105" class="Symbol">(</a><a id="8106" href="simple_essence.html#8002" class="Bound">a</a> <a id="8108" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="8110" href="simple_essence.html#8006" class="Bound">c</a><a id="8111" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8117" href="simple_essence.html#8117" class="Field">·-comm-⊛</a>    <a id="8129" class="Symbol">:</a> <a id="8131" class="Symbol">∀</a> <a id="8133" class="Symbol">{</a><a id="8134" href="simple_essence.html#8134" class="Bound">s</a> <a id="8136" class="Symbol">:</a> <a id="8138" href="simple_essence.html#5990" class="Datatype">§</a><a id="8139" class="Symbol">}</a> <a id="8141" class="Symbol">{</a><a id="8142" href="simple_essence.html#8142" class="Bound">a</a> <a id="8144" href="simple_essence.html#8144" class="Bound">b</a> <a id="8146" class="Symbol">:</a> <a id="8148" href="simple_essence.html#7675" class="Bound">A</a><a id="8149" class="Symbol">}</a>
                  <a id="8169" class="Comment">-------------------------</a>
                <a id="8211" class="Symbol">→</a> <a id="8213" href="simple_essence.html#8142" class="Bound">a</a> <a id="8215" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="8217" class="Symbol">(</a><a id="8218" href="simple_essence.html#8134" class="Bound">s</a> <a id="8220" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="8222" href="simple_essence.html#8144" class="Bound">b</a><a id="8223" class="Symbol">)</a> <a id="8225" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8227" href="simple_essence.html#8134" class="Bound">s</a> <a id="8229" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="8231" class="Symbol">(</a><a id="8232" href="simple_essence.html#8142" class="Bound">a</a> <a id="8234" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="8236" href="simple_essence.html#8144" class="Bound">b</a><a id="8237" class="Symbol">)</a>
    <a id="8243" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8327" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8385" href="simple_essence.html#8385" class="Field">orthonormal</a> <a id="8397" class="Symbol">:</a> <a id="8399" class="Symbol">∀</a> <a id="8401" class="Symbol">{</a><a id="8402" href="simple_essence.html#8402" class="Bound">f</a> <a id="8404" class="Symbol">:</a> <a id="8406" href="simple_essence.html#7675" class="Bound">A</a> <a id="8408" class="Symbol">→</a> <a id="8410" href="simple_essence.html#5990" class="Datatype">§</a><a id="8411" class="Symbol">}</a>
                <a id="8429" class="Symbol">→</a> <a id="8431" class="Symbol">{</a><a id="8432" href="simple_essence.html#8432" class="Bound">x</a> <a id="8434" class="Symbol">:</a> <a id="8436" href="simple_essence.html#7675" class="Bound">A</a><a id="8437" class="Symbol">}</a>
                  <a id="8457" class="Comment">----------------------------------------------------------</a>
                <a id="8532" class="Symbol">→</a> <a id="8534" class="Symbol">(</a><a id="8535" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8541" class="Symbol">(λ</a> <a id="8544" href="simple_essence.html#8544" class="Bound">acc</a> <a id="8548" href="simple_essence.html#8548" class="Bound">v</a> <a id="8550" class="Symbol">→</a> <a id="8552" href="simple_essence.html#8544" class="Bound">acc</a> <a id="8556" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="8558" class="Symbol">(</a><a id="8559" href="simple_essence.html#8402" class="Bound">f</a> <a id="8561" href="simple_essence.html#8548" class="Bound">v</a><a id="8562" class="Symbol">)</a> <a id="8564" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="8566" href="simple_essence.html#8548" class="Bound">v</a><a id="8567" class="Symbol">)</a> <a id="8569" href="simple_essence.html#6143" class="Field">id⊕</a> <a id="8573" href="simple_essence.html#7882" class="Field">basisSet</a><a id="8581" class="Symbol">)</a> <a id="8583" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="8585" href="simple_essence.html#8432" class="Bound">x</a> <a id="8587" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8589" href="simple_essence.html#8402" class="Bound">f</a> <a id="8591" href="simple_essence.html#8432" class="Bound">x</a>
<a id="8593" class="Keyword">open</a> <a id="8598" href="simple_essence.html#7662" class="Module">VectorSpace</a> <a id="8610" class="Symbol">{{</a> <a id="8613" class="Symbol">...</a> <a id="8617" class="Symbol">}}</a>

<a id="8621" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8661" href="simple_essence.html#8661" class="Function">a⊸§→a</a> <a id="8667" class="Symbol">:</a> <a id="8669" class="Symbol">{</a><a id="8670" href="simple_essence.html#8670" class="Bound">A</a> <a id="8672" class="Symbol">:</a> <a id="8674" class="PrimitiveType">Set</a> <a id="8678" href="simple_essence.html#5376" class="Bound">a</a><a id="8679" class="Symbol">}</a>
        <a id="8689" class="Symbol">{{</a><a id="8691" href="simple_essence.html#8691" class="Bound">_</a> <a id="8693" class="Symbol">:</a> <a id="8695" href="simple_essence.html#6030" class="Record">Additive</a> <a id="8704" href="simple_essence.html#8670" class="Bound">A</a><a id="8705" class="Symbol">}}</a> <a id="8708" class="Symbol">{{</a><a id="8710" href="simple_essence.html#8710" class="Bound">_</a> <a id="8712" class="Symbol">:</a> <a id="8714" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="8723" href="simple_essence.html#8670" class="Bound">A</a><a id="8724" class="Symbol">}}</a>
        <a id="8735" class="Symbol">{{</a><a id="8737" href="simple_essence.html#8737" class="Bound">_</a> <a id="8739" class="Symbol">:</a> <a id="8741" href="simple_essence.html#7662" class="Record">VectorSpace</a> <a id="8753" href="simple_essence.html#8670" class="Bound">A</a><a id="8754" class="Symbol">}}</a>
        <a id="8765" class="Comment">-------------------------------------</a>
      <a id="8809" class="Symbol">→</a> <a id="8811" href="simple_essence.html#6916" class="Record">LinMap</a> <a id="8818" href="simple_essence.html#8670" class="Bound">A</a> <a id="8820" href="simple_essence.html#5990" class="Datatype">§</a> <a id="8822" class="Symbol">→</a> <a id="8824" href="simple_essence.html#8670" class="Bound">A</a>
<a id="8826" href="simple_essence.html#8661" class="Function">a⊸§→a</a> <a id="8832" class="Symbol">=</a> <a id="8834" class="Symbol">λ</a> <a id="8836" class="Symbol">{</a> <a id="8838" href="simple_essence.html#8838" class="Bound">lm</a> <a id="8841" class="Symbol">→</a> <a id="8843" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8849" class="Symbol">(λ</a> <a id="8852" href="simple_essence.html#8852" class="Bound">acc</a> <a id="8856" href="simple_essence.html#8856" class="Bound">v</a> <a id="8858" class="Symbol">→</a> <a id="8860" href="simple_essence.html#8852" class="Bound">acc</a> <a id="8864" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="8866" class="Symbol">(</a><a id="8867" href="simple_essence.html#7110" class="Field">LinMap.f</a> <a id="8876" href="simple_essence.html#8838" class="Bound">lm</a> <a id="8879" href="simple_essence.html#8856" class="Bound">v</a><a id="8880" class="Symbol">)</a> <a id="8882" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="8884" href="simple_essence.html#8856" class="Bound">v</a><a id="8885" class="Symbol">)</a> <a id="8887" href="simple_essence.html#6143" class="Field">id⊕</a> <a id="8891" href="simple_essence.html#7882" class="Field">basisSet</a> <a id="8900" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="8903" href="simple_essence.html#8903" class="Function">a⊸§←a</a> <a id="8909" class="Symbol">:</a> <a id="8911" class="Symbol">{</a><a id="8912" href="simple_essence.html#8912" class="Bound">A</a> <a id="8914" class="Symbol">:</a> <a id="8916" class="PrimitiveType">Set</a> <a id="8920" href="simple_essence.html#5376" class="Bound">a</a><a id="8921" class="Symbol">}</a>
        <a id="8931" class="Symbol">{{</a><a id="8933" href="simple_essence.html#8933" class="Bound">_</a> <a id="8935" class="Symbol">:</a> <a id="8937" href="simple_essence.html#6030" class="Record">Additive</a> <a id="8946" href="simple_essence.html#8912" class="Bound">A</a><a id="8947" class="Symbol">}}</a> <a id="8950" class="Symbol">{{</a><a id="8952" href="simple_essence.html#8952" class="Bound">_</a> <a id="8954" class="Symbol">:</a> <a id="8956" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="8965" href="simple_essence.html#8912" class="Bound">A</a><a id="8966" class="Symbol">}}</a>
        <a id="8977" class="Symbol">{{</a><a id="8979" href="simple_essence.html#8979" class="Bound">_</a> <a id="8981" class="Symbol">:</a> <a id="8983" href="simple_essence.html#7662" class="Record">VectorSpace</a> <a id="8995" href="simple_essence.html#8912" class="Bound">A</a><a id="8996" class="Symbol">}}</a>
        <a id="9007" class="Comment">-------------------------------------</a>
      <a id="9051" class="Symbol">→</a> <a id="9053" href="simple_essence.html#8912" class="Bound">A</a> <a id="9055" class="Symbol">→</a> <a id="9057" href="simple_essence.html#6916" class="Record">LinMap</a> <a id="9064" href="simple_essence.html#8912" class="Bound">A</a> <a id="9066" href="simple_essence.html#5990" class="Datatype">§</a>
<a id="9068" href="simple_essence.html#8903" class="Function">a⊸§←a</a> <a id="9074" class="Symbol">=</a> <a id="9076" class="Symbol">λ</a> <a id="9078" class="Symbol">{</a> <a id="9080" href="simple_essence.html#9080" class="Bound">a</a> <a id="9082" class="Symbol">→</a> <a id="9084" href="simple_essence.html#7093" class="InductiveConstructor">mkLM</a> <a id="9089" class="Symbol">(</a><a id="9090" href="simple_essence.html#9080" class="Bound">a</a> <a id="9092" href="simple_essence.html#7907" class="Field Operator">·_</a><a id="9094" class="Symbol">)</a> <a id="9096" href="simple_essence.html#7985" class="Field">·-distrib-⊕</a> <a id="9108" href="simple_essence.html#8117" class="Field">·-comm-⊛</a> <a id="9117" class="Symbol">}</a>

<a id="9120" class="Comment">-- Danger, Will Robinson!</a>
<a id="9146" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9158" href="simple_essence.html#9158" class="Postulate">x·z≡y·z→x≡y</a> <a id="9170" class="Symbol">:</a> <a id="9172" class="Symbol">{</a><a id="9173" href="simple_essence.html#9173" class="Bound">A</a> <a id="9175" class="Symbol">:</a> <a id="9177" class="PrimitiveType">Set</a> <a id="9181" href="simple_essence.html#5376" class="Bound">a</a><a id="9182" class="Symbol">}</a>
                <a id="9200" class="Symbol">{{</a><a id="9202" href="simple_essence.html#9202" class="Bound">_</a> <a id="9204" class="Symbol">:</a> <a id="9206" href="simple_essence.html#6030" class="Record">Additive</a> <a id="9215" href="simple_essence.html#9173" class="Bound">A</a><a id="9216" class="Symbol">}}</a> <a id="9219" class="Symbol">{{</a><a id="9221" href="simple_essence.html#9221" class="Bound">_</a> <a id="9223" class="Symbol">:</a> <a id="9225" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="9234" href="simple_essence.html#9173" class="Bound">A</a><a id="9235" class="Symbol">}}</a> <a id="9238" class="Symbol">{{</a><a id="9240" href="simple_essence.html#9240" class="Bound">_</a> <a id="9242" class="Symbol">:</a> <a id="9244" href="simple_essence.html#7662" class="Record">VectorSpace</a> <a id="9256" href="simple_essence.html#9173" class="Bound">A</a><a id="9257" class="Symbol">}}</a>
                <a id="9276" class="Symbol">{</a><a id="9277" href="simple_essence.html#9277" class="Bound">x</a> <a id="9279" href="simple_essence.html#9279" class="Bound">y</a> <a id="9281" class="Symbol">:</a> <a id="9283" href="simple_essence.html#9173" class="Bound">A</a><a id="9284" class="Symbol">}</a>
              <a id="9300" class="Symbol">→</a> <a id="9302" class="Symbol">(∀</a> <a id="9305" class="Symbol">{</a><a id="9306" href="simple_essence.html#9306" class="Bound">z</a> <a id="9308" class="Symbol">:</a> <a id="9310" href="simple_essence.html#9173" class="Bound">A</a><a id="9311" class="Symbol">}</a> <a id="9313" class="Symbol">→</a> <a id="9315" href="simple_essence.html#9277" class="Bound">x</a> <a id="9317" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="9319" href="simple_essence.html#9306" class="Bound">z</a> <a id="9321" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9323" href="simple_essence.html#9279" class="Bound">y</a> <a id="9325" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="9327" href="simple_essence.html#9306" class="Bound">z</a><a id="9328" class="Symbol">)</a>
                <a id="9346" class="Comment">-----------------------------------------------------------</a>
              <a id="9420" class="Symbol">→</a> <a id="9422" href="simple_essence.html#9277" class="Bound">x</a> <a id="9424" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9426" href="simple_essence.html#9279" class="Bound">y</a>
<a id="9428" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9488" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9555" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9586" href="simple_essence.html#9586" class="Function">a⊸§↔a</a> <a id="9592" class="Symbol">:</a> <a id="9594" class="Symbol">{</a><a id="9595" href="simple_essence.html#9595" class="Bound">A</a> <a id="9597" class="Symbol">:</a> <a id="9599" class="PrimitiveType">Set</a> <a id="9603" href="simple_essence.html#5376" class="Bound">a</a><a id="9604" class="Symbol">}</a>
        <a id="9614" class="Symbol">{{</a><a id="9616" href="simple_essence.html#9616" class="Bound">_</a> <a id="9618" class="Symbol">:</a> <a id="9620" href="simple_essence.html#6030" class="Record">Additive</a> <a id="9629" href="simple_essence.html#9595" class="Bound">A</a><a id="9630" class="Symbol">}}</a> <a id="9633" class="Symbol">{{</a><a id="9635" href="simple_essence.html#9635" class="Bound">_</a> <a id="9637" class="Symbol">:</a> <a id="9639" href="simple_essence.html#6644" class="Record">Scalable</a> <a id="9648" href="simple_essence.html#9595" class="Bound">A</a><a id="9649" class="Symbol">}}</a>
        <a id="9660" class="Symbol">{{</a><a id="9662" href="simple_essence.html#9662" class="Bound">_</a> <a id="9664" class="Symbol">:</a> <a id="9666" href="simple_essence.html#7662" class="Record">VectorSpace</a> <a id="9678" href="simple_essence.html#9595" class="Bound">A</a><a id="9679" class="Symbol">}}</a>
        <a id="9690" class="Comment">-------------------------------------</a>
      <a id="9734" class="Symbol">→</a> <a id="9736" class="Symbol">(</a><a id="9737" href="simple_essence.html#6916" class="Record">LinMap</a> <a id="9744" href="simple_essence.html#9595" class="Bound">A</a> <a id="9746" href="simple_essence.html#5990" class="Datatype">§</a><a id="9747" class="Symbol">)</a> <a id="9749" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9751" href="simple_essence.html#9595" class="Bound">A</a>
<a id="9753" href="simple_essence.html#9586" class="Function">a⊸§↔a</a> <a id="9759" class="Symbol">{</a><a id="9760" href="simple_essence.html#9760" class="Bound">A</a><a id="9761" class="Symbol">}</a> <a id="9763" class="Symbol">=</a>
  <a id="9767" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9771" class="Symbol">{</a><a id="9772" class="Argument">f</a> <a id="9774" class="Symbol">=</a> <a id="9776" href="simple_essence.html#8661" class="Function">a⊸§→a</a><a id="9781" class="Symbol">}</a> <a id="9783" class="Symbol">{</a><a id="9784" class="Argument">f⁻¹</a> <a id="9788" class="Symbol">=</a> <a id="9790" href="simple_essence.html#8903" class="Function">a⊸§←a</a><a id="9795" class="Symbol">}</a>
      <a id="9803" class="Symbol">(</a> <a id="9805" class="Symbol">(λ</a> <a id="9808" class="Symbol">{</a><a id="9809" href="simple_essence.html#9809" class="Bound">x</a> <a id="9811" class="Symbol">→</a> <a id="9813" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="9837" href="simple_essence.html#8661" class="Function">a⊸§→a</a> <a id="9843" class="Symbol">(</a><a id="9844" href="simple_essence.html#8903" class="Function">a⊸§←a</a> <a id="9850" href="simple_essence.html#9809" class="Bound">x</a><a id="9851" class="Symbol">)</a>
                <a id="9869" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9891" href="simple_essence.html#8661" class="Function">a⊸§→a</a> <a id="9897" class="Symbol">(</a><a id="9898" href="simple_essence.html#7093" class="InductiveConstructor">mkLM</a> <a id="9903" class="Symbol">(</a><a id="9904" href="simple_essence.html#9809" class="Bound">x</a> <a id="9906" href="simple_essence.html#7907" class="Field Operator">·_</a><a id="9908" class="Symbol">)</a> <a id="9910" href="simple_essence.html#7985" class="Field">·-distrib-⊕</a> <a id="9922" href="simple_essence.html#8117" class="Field">·-comm-⊛</a><a id="9930" class="Symbol">)</a>
                <a id="9948" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9970" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="9976" class="Symbol">(λ</a> <a id="9979" href="simple_essence.html#9979" class="Bound">acc</a> <a id="9983" href="simple_essence.html#9983" class="Bound">v</a> <a id="9985" class="Symbol">→</a> <a id="9987" href="simple_essence.html#9979" class="Bound">acc</a> <a id="9991" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="9993" class="Symbol">(</a><a id="9994" href="simple_essence.html#9809" class="Bound">x</a> <a id="9996" href="simple_essence.html#7907" class="Field Operator">·</a> <a id="9998" href="simple_essence.html#9983" class="Bound">v</a><a id="9999" class="Symbol">)</a> <a id="10001" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="10003" href="simple_essence.html#9983" class="Bound">v</a><a id="10004" class="Symbol">)</a> <a id="10006" href="simple_essence.html#6143" class="Field">id⊕</a> <a id="10010" href="simple_essence.html#7882" class="Field">basisSet</a>
                <a id="10035" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10038" href="simple_essence.html#9158" class="Postulate">x·z≡y·z→x≡y</a> <a id="10050" class="Symbol">(</a><a id="10051" href="simple_essence.html#8385" class="Field">orthonormal</a> <a id="10063" class="Symbol">{</a><a id="10064" class="Argument">f</a> <a id="10066" class="Symbol">=</a> <a id="10068" class="Symbol">(</a><a id="10069" href="simple_essence.html#9809" class="Bound">x</a> <a id="10071" href="simple_essence.html#7907" class="Field Operator">·_</a><a id="10073" class="Symbol">)})</a> <a id="10077" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10097" href="simple_essence.html#9809" class="Bound">x</a>
                <a id="10115" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10116" class="Symbol">})</a>
      <a id="10125" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10127" class="Symbol">λ</a> <a id="10129" class="Symbol">{</a><a id="10130" href="simple_essence.html#10130" class="Bound">lm</a> <a id="10133" class="Symbol">→</a> <a id="10135" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10159" href="simple_essence.html#8903" class="Function">a⊸§←a</a> <a id="10165" class="Symbol">(</a><a id="10166" href="simple_essence.html#8661" class="Function">a⊸§→a</a> <a id="10172" href="simple_essence.html#10130" class="Bound">lm</a><a id="10174" class="Symbol">)</a>
                <a id="10192" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10214" href="simple_essence.html#8903" class="Function">a⊸§←a</a> <a id="10220" class="Symbol">(</a><a id="10221" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10227" class="Symbol">(λ</a> <a id="10230" href="simple_essence.html#10230" class="Bound">acc</a> <a id="10234" href="simple_essence.html#10234" class="Bound">v</a> <a id="10236" class="Symbol">→</a> <a id="10238" href="simple_essence.html#10230" class="Bound">acc</a> <a id="10242" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="10244" class="Symbol">(</a><a id="10245" href="simple_essence.html#7110" class="Field">LinMap.f</a> <a id="10254" href="simple_essence.html#10130" class="Bound">lm</a> <a id="10257" href="simple_essence.html#10234" class="Bound">v</a><a id="10258" class="Symbol">)</a> <a id="10260" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="10262" href="simple_essence.html#10234" class="Bound">v</a><a id="10263" class="Symbol">)</a> <a id="10265" href="simple_essence.html#6143" class="Field">id⊕</a> <a id="10269" href="simple_essence.html#7882" class="Field">basisSet</a><a id="10277" class="Symbol">)</a>
                <a id="10295" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10317" href="simple_essence.html#7093" class="InductiveConstructor">mkLM</a> <a id="10322" class="Symbol">((</a><a id="10324" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10330" class="Symbol">(λ</a> <a id="10333" href="simple_essence.html#10333" class="Bound">acc</a> <a id="10337" href="simple_essence.html#10337" class="Bound">v</a> <a id="10339" class="Symbol">→</a> <a id="10341" href="simple_essence.html#10333" class="Bound">acc</a> <a id="10345" href="simple_essence.html#6156" class="Field Operator">⊕</a> <a id="10347" class="Symbol">(</a><a id="10348" href="simple_essence.html#7110" class="Field">LinMap.f</a> <a id="10357" href="simple_essence.html#10130" class="Bound">lm</a> <a id="10360" href="simple_essence.html#10337" class="Bound">v</a><a id="10361" class="Symbol">)</a> <a id="10363" href="simple_essence.html#6757" class="Field Operator">⊛</a> <a id="10365" href="simple_essence.html#10337" class="Bound">v</a><a id="10366" class="Symbol">)</a> <a id="10368" href="simple_essence.html#6143" class="Field">id⊕</a> <a id="10372" href="simple_essence.html#7882" class="Field">basisSet</a><a id="10380" class="Symbol">)</a><a id="10381" href="simple_essence.html#7907" class="Field Operator">·_</a><a id="10383" class="Symbol">)</a>
                       <a id="10408" href="simple_essence.html#7985" class="Field">·-distrib-⊕</a> <a id="10420" href="simple_essence.html#8117" class="Field">·-comm-⊛</a>
                <a id="10445" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10448" href="simple_essence.html#7428" class="Postulate">⊸≡</a> <a id="10451" class="Symbol">(</a> <a id="10453" href="simple_essence.html#5909" class="Postulate">extensionality</a>
                          <a id="10494" class="Symbol">(</a> <a id="10496" class="Symbol">λ</a> <a id="10498" href="simple_essence.html#10498" class="Bound">x</a> <a id="10500" class="Symbol">→</a> <a id="10502" href="simple_essence.html#8385" class="Field">orthonormal</a> <a id="10514" class="Symbol">{</a><a id="10515" class="Argument">f</a> <a id="10517" class="Symbol">=</a> <a id="10519" href="simple_essence.html#7110" class="Field">LinMap.f</a> <a id="10528" href="simple_essence.html#10130" class="Bound">lm</a><a id="10530" class="Symbol">}</a> <a id="10532" class="Symbol">{</a><a id="10533" class="Argument">x</a> <a id="10535" class="Symbol">=</a> <a id="10537" href="simple_essence.html#10498" class="Bound">x</a><a id="10538" class="Symbol">}</a> <a id="10540" class="Symbol">)</a>
                      <a id="10564" class="Symbol">)</a>
                 <a id="10583" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10603" href="simple_essence.html#10130" class="Bound">lm</a>
                <a id="10622" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10623" class="Symbol">}</a>
      <a id="10631" class="Symbol">)</a>

<a id="10634" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10717" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10779" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="10873" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="10936" class="Comment">--</a>
<a id="10939" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="10962" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="11011" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="11044" class="Comment">--         -------------------------------------</a>
<a id="11093" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11121" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>