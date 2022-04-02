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

And that, therefore, since $a ⊸ s$ is isomorphic to $a$,  $(b ⊸ s) → (a ⊸ s)$ is indeed isomorphic to $b → a$.

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

<pre class="Agda"><a id="5349" class="Keyword">module</a> <a id="5356" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5371" class="Symbol">{</a><a id="5372" href="simple_essence.html#5372" class="Bound">s</a> <a id="5374" href="simple_essence.html#5374" class="Bound">a</a> <a id="5376" href="simple_essence.html#5376" class="Bound">b</a><a id="5377" class="Symbol">}</a> <a id="5379" class="Keyword">where</a>

<a id="5386" class="Keyword">open</a> <a id="5391" class="Keyword">import</a> <a id="5398" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5417" class="Keyword">open</a> <a id="5422" class="Keyword">import</a> <a id="5429" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5464" class="Keyword">using</a> <a id="5470" class="Symbol">(</a><a id="5471" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5485" class="Symbol">)</a>
<a id="5487" class="Keyword">open</a> <a id="5492" class="Keyword">import</a> <a id="5499" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5510" class="Keyword">open</a> <a id="5515" class="Keyword">import</a> <a id="5522" href="Data.List.html" class="Module">Data.List</a>
<a id="5532" class="Keyword">open</a> <a id="5537" class="Keyword">import</a> <a id="5544" href="Function.html" class="Module">Function</a> <a id="5553" class="Keyword">using</a> <a id="5559" class="Symbol">(</a><a id="5560" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5563" class="Symbol">;</a> <a id="5565" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5568" class="Symbol">;</a> <a id="5570" href="Function.Base.html#615" class="Function">id</a><a id="5572" class="Symbol">)</a>
<a id="5574" class="Keyword">open</a> <a id="5579" class="Keyword">import</a> <a id="5586" href="Level.html" class="Module">Level</a> <a id="5592" class="Keyword">using</a> <a id="5598" class="Symbol">(</a><a id="5599" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5604" class="Symbol">;</a> <a id="5606" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5609" class="Symbol">)</a>

<a id="5612" class="Keyword">import</a> <a id="5619" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5657" class="Symbol">as</a> <a id="5660" class="Module">Eq</a>
<a id="5663" class="Keyword">open</a> <a id="5668" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5671" class="Keyword">using</a> <a id="5677" class="Symbol">(</a><a id="5678" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5681" class="Symbol">;</a> <a id="5683" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5687" class="Symbol">;</a> <a id="5689" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5694" class="Symbol">;</a> <a id="5696" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5699" class="Symbol">;</a> <a id="5701" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5705" class="Symbol">;</a> <a id="5707" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5712" class="Symbol">;</a> <a id="5714" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5722" class="Symbol">;</a> <a id="5724" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5729" class="Symbol">)</a>
<a id="5731" class="Keyword">open</a> <a id="5736" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5751" class="Keyword">using</a> <a id="5757" class="Symbol">(</a><a id="5758" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5764" class="Symbol">;</a> <a id="5766" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5771" class="Symbol">;</a> <a id="5773" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5779" class="Symbol">;</a> <a id="5781" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5783" class="Symbol">)</a>

<a id="5786" class="Keyword">postulate</a>
  <a id="5798" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="5873" href="simple_essence.html#5873" class="Postulate">id+</a> <a id="5877" class="Symbol">:</a> <a id="5879" class="Symbol">{</a><a id="5880" href="simple_essence.html#5880" class="Bound">x</a> <a id="5882" class="Symbol">:</a> <a id="5884" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="5889" class="Symbol">}</a> <a id="5891" class="Symbol">→</a> <a id="5893" class="Number">0.0</a> <a id="5897" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="5899" href="simple_essence.html#5880" class="Bound">x</a> <a id="5901" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5903" href="simple_essence.html#5880" class="Bound">x</a>
  <a id="extensionality"></a><a id="5907" href="simple_essence.html#5907" class="Postulate">extensionality</a> <a id="5922" class="Symbol">:</a> <a id="5924" class="Symbol">∀</a> <a id="5926" class="Symbol">{</a><a id="5927" href="simple_essence.html#5927" class="Bound">ℓ₁</a> <a id="5930" href="simple_essence.html#5930" class="Bound">ℓ₂</a><a id="5932" class="Symbol">}</a> <a id="5934" class="Symbol">→</a> <a id="5936" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="5951" href="simple_essence.html#5927" class="Bound">ℓ₁</a> <a id="5954" href="simple_essence.html#5930" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="5958" href="simple_essence.html#5958" class="Function">ℓ</a> <a id="5960" class="Symbol">:</a> <a id="5962" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="5968" href="simple_essence.html#5958" class="Function">ℓ</a> <a id="5970" class="Symbol">=</a> <a id="5972" href="simple_essence.html#5372" class="Bound">s</a> <a id="5974" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5976" href="simple_essence.html#5374" class="Bound">a</a> <a id="5978" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5980" href="simple_essence.html#5376" class="Bound">b</a>

<a id="5983" class="Keyword">data</a> <a id="§"></a><a id="5988" href="simple_essence.html#5988" class="Datatype">§</a> <a id="5990" class="Symbol">:</a> <a id="5992" class="PrimitiveType">Set</a> <a id="5996" href="simple_essence.html#5374" class="Bound">a</a> <a id="5998" class="Keyword">where</a>
  <a id="§.S"></a><a id="6006" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6008" class="Symbol">:</a> <a id="6010" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="6016" class="Symbol">→</a> <a id="6018" href="simple_essence.html#5988" class="Datatype">§</a>

<a id="6021" class="Keyword">record</a> <a id="Additive"></a><a id="6028" href="simple_essence.html#6028" class="Record">Additive</a> <a id="6037" class="Symbol">(</a><a id="6038" href="simple_essence.html#6038" class="Bound">A</a> <a id="6040" class="Symbol">:</a> <a id="6042" class="PrimitiveType">Set</a> <a id="6046" href="simple_essence.html#5374" class="Bound">a</a><a id="6047" class="Symbol">)</a> <a id="6049" class="Symbol">:</a> <a id="6051" class="PrimitiveType">Set</a> <a id="6055" href="simple_essence.html#5958" class="Function">ℓ</a> <a id="6057" class="Keyword">where</a>
  <a id="6065" class="Keyword">infixl</a> <a id="6072" class="Number">6</a> <a id="6074" href="simple_essence.html#6154" class="Field Operator">_⊕_</a>  <a id="6079" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6131" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6141" href="simple_essence.html#6141" class="Field">id⊕</a>  <a id="6146" class="Symbol">:</a> <a id="6148" href="simple_essence.html#6038" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6154" href="simple_essence.html#6154" class="Field Operator">_⊕_</a>  <a id="6159" class="Symbol">:</a> <a id="6161" href="simple_essence.html#6038" class="Bound">A</a> <a id="6163" class="Symbol">→</a> <a id="6165" href="simple_essence.html#6038" class="Bound">A</a> <a id="6167" class="Symbol">→</a> <a id="6169" href="simple_essence.html#6038" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6175" href="simple_essence.html#6175" class="Field">id-⊕</a> <a id="6180" class="Symbol">:</a> <a id="6182" class="Symbol">(</a><a id="6183" href="simple_essence.html#6183" class="Bound">a</a> <a id="6185" class="Symbol">:</a> <a id="6187" href="simple_essence.html#6038" class="Bound">A</a><a id="6188" class="Symbol">)</a>
           <a id="6201" class="Comment">-----------</a>
         <a id="6222" class="Symbol">→</a> <a id="6224" href="simple_essence.html#6141" class="Field">id⊕</a> <a id="6228" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="6230" href="simple_essence.html#6183" class="Bound">a</a> <a id="6232" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6234" href="simple_essence.html#6183" class="Bound">a</a>
    <a id="6240" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6293" class="Keyword">open</a> <a id="6298" href="simple_essence.html#6028" class="Module">Additive</a> <a id="6307" class="Symbol">{{</a> <a id="6310" class="Symbol">...</a> <a id="6314" class="Symbol">}}</a>
<a id="6317" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6328" href="simple_essence.html#6328" class="Function">AdditiveScalar</a> <a id="6343" class="Symbol">:</a> <a id="6345" href="simple_essence.html#6028" class="Record">Additive</a> <a id="6354" href="simple_essence.html#5988" class="Datatype">§</a>
  <a id="6358" href="simple_essence.html#6328" class="Function">AdditiveScalar</a> <a id="6373" class="Symbol">=</a> <a id="6375" class="Keyword">record</a>
    <a id="6386" class="Symbol">{</a> <a id="6388" href="simple_essence.html#6141" class="Field">id⊕</a>  <a id="6393" class="Symbol">=</a> <a id="6395" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6397" class="Number">0.0</a>
    <a id="6405" class="Symbol">;</a> <a id="6407" href="simple_essence.html#6154" class="Field Operator">_⊕_</a>  <a id="6412" class="Symbol">=</a> <a id="6414" class="Symbol">λ</a> <a id="6416" class="Symbol">{(</a><a id="6418" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6420" href="simple_essence.html#6420" class="Bound">x</a><a id="6421" class="Symbol">)</a> <a id="6423" class="Symbol">(</a><a id="6424" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6426" href="simple_essence.html#6426" class="Bound">y</a><a id="6427" class="Symbol">)</a> <a id="6429" class="Symbol">→</a> <a id="6431" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6433" class="Symbol">(</a><a id="6434" href="simple_essence.html#6420" class="Bound">x</a> <a id="6436" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6438" href="simple_essence.html#6426" class="Bound">y</a><a id="6439" class="Symbol">)}</a>
    <a id="6446" class="Symbol">;</a> <a id="6448" href="simple_essence.html#6175" class="Field">id-⊕</a> <a id="6453" class="Symbol">=</a> <a id="6455" class="Symbol">λ</a> <a id="6457" class="Symbol">{</a> <a id="6459" class="Symbol">(</a><a id="6460" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6462" href="simple_essence.html#6462" class="Bound">x</a><a id="6463" class="Symbol">)</a> <a id="6465" class="Symbol">→</a> <a id="6467" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6500" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6502" class="Symbol">(</a><a id="6503" class="Number">0.0</a> <a id="6507" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6509" href="simple_essence.html#6462" class="Bound">x</a><a id="6510" class="Symbol">)</a>
                         <a id="6537" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6540" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6545" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6547" href="simple_essence.html#5873" class="Postulate">id+</a> <a id="6551" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6580" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6582" href="simple_essence.html#6462" class="Bound">x</a>
                         <a id="6609" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6626" class="Symbol">}</a>
    <a id="6632" class="Symbol">}</a>

<a id="6635" class="Keyword">record</a> <a id="Scalable"></a><a id="6642" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="6651" class="Symbol">(</a><a id="6652" href="simple_essence.html#6652" class="Bound">A</a> <a id="6654" class="Symbol">:</a> <a id="6656" class="PrimitiveType">Set</a> <a id="6660" href="simple_essence.html#5374" class="Bound">a</a><a id="6661" class="Symbol">)</a> <a id="6663" class="Symbol">:</a> <a id="6665" class="PrimitiveType">Set</a> <a id="6669" href="simple_essence.html#5958" class="Function">ℓ</a> <a id="6671" class="Keyword">where</a>
  <a id="6679" class="Keyword">infixl</a> <a id="6686" class="Number">7</a> <a id="6688" href="simple_essence.html#6755" class="Field Operator">_⊛_</a>  <a id="6693" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6745" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6755" href="simple_essence.html#6755" class="Field Operator">_⊛_</a> <a id="6759" class="Symbol">:</a> <a id="6761" href="simple_essence.html#5988" class="Datatype">§</a> <a id="6763" class="Symbol">→</a> <a id="6765" href="simple_essence.html#6652" class="Bound">A</a> <a id="6767" class="Symbol">→</a> <a id="6769" href="simple_essence.html#6652" class="Bound">A</a>
<a id="6771" class="Keyword">open</a> <a id="6776" href="simple_essence.html#6642" class="Module">Scalable</a> <a id="6785" class="Symbol">{{</a> <a id="6788" class="Symbol">...</a> <a id="6792" class="Symbol">}}</a>
<a id="6795" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="6806" href="simple_essence.html#6806" class="Function">ScalableScalar</a> <a id="6821" class="Symbol">:</a> <a id="6823" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="6832" href="simple_essence.html#5988" class="Datatype">§</a>
  <a id="6836" href="simple_essence.html#6806" class="Function">ScalableScalar</a> <a id="6851" class="Symbol">=</a> <a id="6853" class="Keyword">record</a>
    <a id="6864" class="Symbol">{</a> <a id="6866" href="simple_essence.html#6755" class="Field Operator">_⊛_</a> <a id="6870" class="Symbol">=</a> <a id="6872" class="Symbol">λ</a> <a id="6874" class="Symbol">{(</a><a id="6876" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6878" href="simple_essence.html#6878" class="Bound">x</a><a id="6879" class="Symbol">)</a> <a id="6881" class="Symbol">(</a><a id="6882" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6884" href="simple_essence.html#6884" class="Bound">y</a><a id="6885" class="Symbol">)</a> <a id="6887" class="Symbol">→</a> <a id="6889" href="simple_essence.html#6006" class="InductiveConstructor">S</a> <a id="6891" class="Symbol">(</a><a id="6892" href="simple_essence.html#6878" class="Bound">x</a> <a id="6894" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="6896" href="simple_essence.html#6884" class="Bound">y</a><a id="6897" class="Symbol">)}</a>
    <a id="6904" class="Symbol">}</a>

<a id="6907" class="Keyword">record</a> <a id="LinMap"></a><a id="6914" href="simple_essence.html#6914" class="Record">LinMap</a> <a id="6921" class="Symbol">(</a><a id="6922" href="simple_essence.html#6922" class="Bound">A</a> <a id="6924" class="Symbol">:</a> <a id="6926" class="PrimitiveType">Set</a> <a id="6930" href="simple_essence.html#5374" class="Bound">a</a><a id="6931" class="Symbol">)</a> <a id="6933" class="Symbol">(</a><a id="6934" href="simple_essence.html#6934" class="Bound">B</a> <a id="6936" class="Symbol">:</a> <a id="6938" class="PrimitiveType">Set</a> <a id="6942" href="simple_essence.html#5374" class="Bound">a</a><a id="6943" class="Symbol">)</a>
              <a id="6959" class="Symbol">{{</a><a id="6961" href="simple_essence.html#6961" class="Bound">_</a> <a id="6963" class="Symbol">:</a> <a id="6965" href="simple_essence.html#6028" class="Record">Additive</a> <a id="6974" href="simple_essence.html#6922" class="Bound">A</a><a id="6975" class="Symbol">}}</a> <a id="6978" class="Symbol">{{</a><a id="6980" href="simple_essence.html#6980" class="Bound">_</a> <a id="6982" class="Symbol">:</a> <a id="6984" href="simple_essence.html#6028" class="Record">Additive</a> <a id="6993" href="simple_essence.html#6934" class="Bound">B</a><a id="6994" class="Symbol">}}</a>
              <a id="7011" class="Symbol">{{</a><a id="7013" href="simple_essence.html#7013" class="Bound">_</a> <a id="7015" class="Symbol">:</a> <a id="7017" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="7026" href="simple_essence.html#6922" class="Bound">A</a><a id="7027" class="Symbol">}}</a> <a id="7030" class="Symbol">{{</a><a id="7032" href="simple_essence.html#7032" class="Bound">_</a> <a id="7034" class="Symbol">:</a> <a id="7036" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="7045" href="simple_essence.html#6934" class="Bound">B</a><a id="7046" class="Symbol">}}</a>
              <a id="7063" class="Symbol">:</a> <a id="7065" class="PrimitiveType">Set</a> <a id="7069" href="simple_essence.html#5958" class="Function">ℓ</a> <a id="7071" class="Keyword">where</a>
  <a id="7079" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7091" href="simple_essence.html#7091" class="InductiveConstructor">mkLM</a>
  <a id="7098" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7108" href="simple_essence.html#7108" class="Field">f</a>      <a id="7115" class="Symbol">:</a> <a id="7117" href="simple_essence.html#6922" class="Bound">A</a> <a id="7119" class="Symbol">→</a> <a id="7121" href="simple_essence.html#6934" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7128" href="simple_essence.html#7128" class="Field">adds</a>   <a id="7135" class="Symbol">:</a> <a id="7137" class="Symbol">∀</a> <a id="7139" class="Symbol">{</a><a id="7140" href="simple_essence.html#7140" class="Bound">a</a> <a id="7142" href="simple_essence.html#7142" class="Bound">b</a> <a id="7144" class="Symbol">:</a> <a id="7146" href="simple_essence.html#6922" class="Bound">A</a><a id="7147" class="Symbol">}</a>
             <a id="7162" class="Comment">---------------------</a>
           <a id="7195" class="Symbol">→</a> <a id="7197" href="simple_essence.html#7108" class="Field">f</a> <a id="7199" class="Symbol">(</a><a id="7200" href="simple_essence.html#7140" class="Bound">a</a> <a id="7202" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="7204" href="simple_essence.html#7142" class="Bound">b</a><a id="7205" class="Symbol">)</a> <a id="7207" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7209" href="simple_essence.html#7108" class="Field">f</a> <a id="7211" href="simple_essence.html#7140" class="Bound">a</a> <a id="7213" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="7215" href="simple_essence.html#7108" class="Field">f</a> <a id="7217" href="simple_essence.html#7142" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7224" href="simple_essence.html#7224" class="Field">scales</a> <a id="7231" class="Symbol">:</a> <a id="7233" class="Symbol">∀</a> <a id="7235" class="Symbol">{</a><a id="7236" href="simple_essence.html#7236" class="Bound">s</a> <a id="7238" class="Symbol">:</a> <a id="7240" href="simple_essence.html#5988" class="Datatype">§</a><a id="7241" class="Symbol">}</a> <a id="7243" class="Symbol">{</a><a id="7244" href="simple_essence.html#7244" class="Bound">a</a> <a id="7246" class="Symbol">:</a> <a id="7248" href="simple_essence.html#6922" class="Bound">A</a><a id="7249" class="Symbol">}</a>
             <a id="7264" class="Comment">-------------------</a>
           <a id="7295" class="Symbol">→</a> <a id="7297" href="simple_essence.html#7108" class="Field">f</a> <a id="7299" class="Symbol">(</a><a id="7300" href="simple_essence.html#7236" class="Bound">s</a> <a id="7302" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="7304" href="simple_essence.html#7244" class="Bound">a</a><a id="7305" class="Symbol">)</a> <a id="7307" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7309" href="simple_essence.html#7236" class="Bound">s</a> <a id="7311" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="7313" href="simple_essence.html#7108" class="Field">f</a> <a id="7315" href="simple_essence.html#7244" class="Bound">a</a>
<a id="7317" class="Keyword">open</a> <a id="7322" href="simple_essence.html#6914" class="Module">LinMap</a> <a id="7329" class="Symbol">{{</a> <a id="7332" class="Symbol">...</a> <a id="7336" class="Symbol">}}</a>

<a id="7340" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7366" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7414" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7426" href="simple_essence.html#7426" class="Postulate">⊸≡</a> <a id="7429" class="Symbol">:</a> <a id="7431" class="Symbol">{</a><a id="7432" href="simple_essence.html#7432" class="Bound">A</a> <a id="7434" href="simple_essence.html#7434" class="Bound">B</a> <a id="7436" class="Symbol">:</a> <a id="7438" class="PrimitiveType">Set</a> <a id="7442" href="simple_essence.html#5374" class="Bound">a</a><a id="7443" class="Symbol">}</a>
       <a id="7452" class="Symbol">{{</a><a id="7454" href="simple_essence.html#7454" class="Bound">_</a> <a id="7456" class="Symbol">:</a> <a id="7458" href="simple_essence.html#6028" class="Record">Additive</a> <a id="7467" href="simple_essence.html#7432" class="Bound">A</a><a id="7468" class="Symbol">}}</a> <a id="7471" class="Symbol">{{</a><a id="7473" href="simple_essence.html#7473" class="Bound">_</a> <a id="7475" class="Symbol">:</a> <a id="7477" href="simple_essence.html#6028" class="Record">Additive</a> <a id="7486" href="simple_essence.html#7434" class="Bound">B</a><a id="7487" class="Symbol">}}</a>
       <a id="7497" class="Symbol">{{</a><a id="7499" href="simple_essence.html#7499" class="Bound">_</a> <a id="7501" class="Symbol">:</a> <a id="7503" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="7512" href="simple_essence.html#7432" class="Bound">A</a><a id="7513" class="Symbol">}}</a> <a id="7516" class="Symbol">{{</a><a id="7518" href="simple_essence.html#7518" class="Bound">_</a> <a id="7520" class="Symbol">:</a> <a id="7522" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="7531" href="simple_essence.html#7434" class="Bound">B</a><a id="7532" class="Symbol">}}</a>
       <a id="7542" class="Symbol">{</a><a id="7543" href="simple_essence.html#7543" class="Bound">lm₁</a> <a id="7547" href="simple_essence.html#7547" class="Bound">lm₂</a> <a id="7551" class="Symbol">:</a> <a id="7553" href="simple_essence.html#6914" class="Record">LinMap</a> <a id="7560" href="simple_essence.html#7432" class="Bound">A</a> <a id="7562" href="simple_essence.html#7434" class="Bound">B</a><a id="7563" class="Symbol">}</a>
     <a id="7570" class="Symbol">→</a> <a id="7572" href="simple_essence.html#7108" class="Field">LinMap.f</a> <a id="7581" href="simple_essence.html#7543" class="Bound">lm₁</a> <a id="7585" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7587" href="simple_essence.html#7108" class="Field">LinMap.f</a> <a id="7596" href="simple_essence.html#7547" class="Bound">lm₂</a>
       <a id="7607" class="Comment">---------------------------</a>
     <a id="7640" class="Symbol">→</a> <a id="7642" href="simple_essence.html#7543" class="Bound">lm₁</a> <a id="7646" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7648" href="simple_essence.html#7547" class="Bound">lm₂</a>

<a id="7653" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7660" href="simple_essence.html#7660" class="Record">VectorSpace</a> <a id="7672" class="Symbol">(</a><a id="7673" href="simple_essence.html#7673" class="Bound">A</a> <a id="7675" class="Symbol">:</a> <a id="7677" class="PrimitiveType">Set</a> <a id="7681" href="simple_essence.html#5374" class="Bound">a</a><a id="7682" class="Symbol">)</a>
                   <a id="7703" class="Symbol">{{</a><a id="7705" href="simple_essence.html#7705" class="Bound">_</a> <a id="7707" class="Symbol">:</a> <a id="7709" href="simple_essence.html#6028" class="Record">Additive</a> <a id="7718" href="simple_essence.html#7673" class="Bound">A</a><a id="7719" class="Symbol">}}</a> <a id="7722" class="Symbol">{{</a><a id="7724" href="simple_essence.html#7724" class="Bound">_</a> <a id="7726" class="Symbol">:</a> <a id="7728" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="7737" href="simple_essence.html#7673" class="Bound">A</a><a id="7738" class="Symbol">}}</a>
                   <a id="7760" class="Symbol">:</a> <a id="7762" class="PrimitiveType">Set</a> <a id="7766" href="simple_essence.html#5958" class="Function">ℓ</a> <a id="7768" class="Keyword">where</a>
  <a id="7776" class="Keyword">field</a>
    <a id="7786" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="7880" href="simple_essence.html#7880" class="Field">basisSet</a>    <a id="7892" class="Symbol">:</a> <a id="7894" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="7899" href="simple_essence.html#7673" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="7905" href="simple_essence.html#7905" class="Field Operator">_·_</a>         <a id="7917" class="Symbol">:</a> <a id="7919" href="simple_essence.html#7673" class="Bound">A</a> <a id="7921" class="Symbol">→</a> <a id="7923" href="simple_essence.html#7673" class="Bound">A</a> <a id="7925" class="Symbol">→</a> <a id="7927" href="simple_essence.html#5988" class="Datatype">§</a>
    <a id="7933" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="7983" href="simple_essence.html#7983" class="Field">·-distrib-⊕</a> <a id="7995" class="Symbol">:</a> <a id="7997" class="Symbol">∀</a> <a id="7999" class="Symbol">{</a><a id="8000" href="simple_essence.html#8000" class="Bound">a</a> <a id="8002" href="simple_essence.html#8002" class="Bound">b</a> <a id="8004" href="simple_essence.html#8004" class="Bound">c</a> <a id="8006" class="Symbol">:</a> <a id="8008" href="simple_essence.html#7673" class="Bound">A</a><a id="8009" class="Symbol">}</a>
                  <a id="8029" class="Comment">-------------------------------</a>
                <a id="8077" class="Symbol">→</a> <a id="8079" href="simple_essence.html#8000" class="Bound">a</a> <a id="8081" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="8083" class="Symbol">(</a><a id="8084" href="simple_essence.html#8002" class="Bound">b</a> <a id="8086" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="8088" href="simple_essence.html#8004" class="Bound">c</a><a id="8089" class="Symbol">)</a> <a id="8091" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8093" class="Symbol">(</a><a id="8094" href="simple_essence.html#8000" class="Bound">a</a> <a id="8096" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="8098" href="simple_essence.html#8002" class="Bound">b</a><a id="8099" class="Symbol">)</a> <a id="8101" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="8103" class="Symbol">(</a><a id="8104" href="simple_essence.html#8000" class="Bound">a</a> <a id="8106" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="8108" href="simple_essence.html#8004" class="Bound">c</a><a id="8109" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8115" href="simple_essence.html#8115" class="Field">·-comm-⊛</a>    <a id="8127" class="Symbol">:</a> <a id="8129" class="Symbol">∀</a> <a id="8131" class="Symbol">{</a><a id="8132" href="simple_essence.html#8132" class="Bound">s</a> <a id="8134" class="Symbol">:</a> <a id="8136" href="simple_essence.html#5988" class="Datatype">§</a><a id="8137" class="Symbol">}</a> <a id="8139" class="Symbol">{</a><a id="8140" href="simple_essence.html#8140" class="Bound">a</a> <a id="8142" href="simple_essence.html#8142" class="Bound">b</a> <a id="8144" class="Symbol">:</a> <a id="8146" href="simple_essence.html#7673" class="Bound">A</a><a id="8147" class="Symbol">}</a>
                  <a id="8167" class="Comment">-------------------------</a>
                <a id="8209" class="Symbol">→</a> <a id="8211" href="simple_essence.html#8140" class="Bound">a</a> <a id="8213" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="8215" class="Symbol">(</a><a id="8216" href="simple_essence.html#8132" class="Bound">s</a> <a id="8218" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="8220" href="simple_essence.html#8142" class="Bound">b</a><a id="8221" class="Symbol">)</a> <a id="8223" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8225" href="simple_essence.html#8132" class="Bound">s</a> <a id="8227" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="8229" class="Symbol">(</a><a id="8230" href="simple_essence.html#8140" class="Bound">a</a> <a id="8232" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="8234" href="simple_essence.html#8142" class="Bound">b</a><a id="8235" class="Symbol">)</a>
    <a id="8241" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8325" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8383" href="simple_essence.html#8383" class="Field">orthonormal</a> <a id="8395" class="Symbol">:</a> <a id="8397" class="Symbol">∀</a> <a id="8399" class="Symbol">{</a><a id="8400" href="simple_essence.html#8400" class="Bound">f</a> <a id="8402" class="Symbol">:</a> <a id="8404" href="simple_essence.html#7673" class="Bound">A</a> <a id="8406" class="Symbol">→</a> <a id="8408" href="simple_essence.html#5988" class="Datatype">§</a><a id="8409" class="Symbol">}</a>
                <a id="8427" class="Symbol">→</a> <a id="8429" class="Symbol">{</a><a id="8430" href="simple_essence.html#8430" class="Bound">x</a> <a id="8432" class="Symbol">:</a> <a id="8434" href="simple_essence.html#7673" class="Bound">A</a><a id="8435" class="Symbol">}</a>
                  <a id="8455" class="Comment">----------------------------------------------------------</a>
                <a id="8530" class="Symbol">→</a> <a id="8532" class="Symbol">(</a><a id="8533" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8539" class="Symbol">(λ</a> <a id="8542" href="simple_essence.html#8542" class="Bound">acc</a> <a id="8546" href="simple_essence.html#8546" class="Bound">v</a> <a id="8548" class="Symbol">→</a> <a id="8550" href="simple_essence.html#8542" class="Bound">acc</a> <a id="8554" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="8556" class="Symbol">(</a><a id="8557" href="simple_essence.html#8400" class="Bound">f</a> <a id="8559" href="simple_essence.html#8546" class="Bound">v</a><a id="8560" class="Symbol">)</a> <a id="8562" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="8564" href="simple_essence.html#8546" class="Bound">v</a><a id="8565" class="Symbol">)</a> <a id="8567" href="simple_essence.html#6141" class="Field">id⊕</a> <a id="8571" href="simple_essence.html#7880" class="Field">basisSet</a><a id="8579" class="Symbol">)</a> <a id="8581" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="8583" href="simple_essence.html#8430" class="Bound">x</a> <a id="8585" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8587" href="simple_essence.html#8400" class="Bound">f</a> <a id="8589" href="simple_essence.html#8430" class="Bound">x</a>
<a id="8591" class="Keyword">open</a> <a id="8596" href="simple_essence.html#7660" class="Module">VectorSpace</a> <a id="8608" class="Symbol">{{</a> <a id="8611" class="Symbol">...</a> <a id="8615" class="Symbol">}}</a>

<a id="8619" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8659" href="simple_essence.html#8659" class="Function">a⊸§→a</a> <a id="8665" class="Symbol">:</a> <a id="8667" class="Symbol">{</a><a id="8668" href="simple_essence.html#8668" class="Bound">A</a> <a id="8670" class="Symbol">:</a> <a id="8672" class="PrimitiveType">Set</a> <a id="8676" href="simple_essence.html#5374" class="Bound">a</a><a id="8677" class="Symbol">}</a>
        <a id="8687" class="Symbol">{{</a><a id="8689" href="simple_essence.html#8689" class="Bound">_</a> <a id="8691" class="Symbol">:</a> <a id="8693" href="simple_essence.html#6028" class="Record">Additive</a> <a id="8702" href="simple_essence.html#8668" class="Bound">A</a><a id="8703" class="Symbol">}}</a> <a id="8706" class="Symbol">{{</a><a id="8708" href="simple_essence.html#8708" class="Bound">_</a> <a id="8710" class="Symbol">:</a> <a id="8712" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="8721" href="simple_essence.html#8668" class="Bound">A</a><a id="8722" class="Symbol">}}</a>
        <a id="8733" class="Symbol">{{</a><a id="8735" href="simple_essence.html#8735" class="Bound">_</a> <a id="8737" class="Symbol">:</a> <a id="8739" href="simple_essence.html#7660" class="Record">VectorSpace</a> <a id="8751" href="simple_essence.html#8668" class="Bound">A</a><a id="8752" class="Symbol">}}</a>
        <a id="8763" class="Comment">-------------------------------------</a>
      <a id="8807" class="Symbol">→</a> <a id="8809" href="simple_essence.html#6914" class="Record">LinMap</a> <a id="8816" href="simple_essence.html#8668" class="Bound">A</a> <a id="8818" href="simple_essence.html#5988" class="Datatype">§</a> <a id="8820" class="Symbol">→</a> <a id="8822" href="simple_essence.html#8668" class="Bound">A</a>
<a id="8824" href="simple_essence.html#8659" class="Function">a⊸§→a</a> <a id="8830" class="Symbol">=</a> <a id="8832" class="Symbol">λ</a> <a id="8834" class="Symbol">{</a> <a id="8836" href="simple_essence.html#8836" class="Bound">lm</a> <a id="8839" class="Symbol">→</a> <a id="8841" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8847" class="Symbol">(λ</a> <a id="8850" href="simple_essence.html#8850" class="Bound">acc</a> <a id="8854" href="simple_essence.html#8854" class="Bound">v</a> <a id="8856" class="Symbol">→</a> <a id="8858" href="simple_essence.html#8850" class="Bound">acc</a> <a id="8862" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="8864" class="Symbol">(</a><a id="8865" href="simple_essence.html#7108" class="Field">LinMap.f</a> <a id="8874" href="simple_essence.html#8836" class="Bound">lm</a> <a id="8877" href="simple_essence.html#8854" class="Bound">v</a><a id="8878" class="Symbol">)</a> <a id="8880" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="8882" href="simple_essence.html#8854" class="Bound">v</a><a id="8883" class="Symbol">)</a> <a id="8885" href="simple_essence.html#6141" class="Field">id⊕</a> <a id="8889" href="simple_essence.html#7880" class="Field">basisSet</a> <a id="8898" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="8901" href="simple_essence.html#8901" class="Function">a⊸§←a</a> <a id="8907" class="Symbol">:</a> <a id="8909" class="Symbol">{</a><a id="8910" href="simple_essence.html#8910" class="Bound">A</a> <a id="8912" class="Symbol">:</a> <a id="8914" class="PrimitiveType">Set</a> <a id="8918" href="simple_essence.html#5374" class="Bound">a</a><a id="8919" class="Symbol">}</a>
        <a id="8929" class="Symbol">{{</a><a id="8931" href="simple_essence.html#8931" class="Bound">_</a> <a id="8933" class="Symbol">:</a> <a id="8935" href="simple_essence.html#6028" class="Record">Additive</a> <a id="8944" href="simple_essence.html#8910" class="Bound">A</a><a id="8945" class="Symbol">}}</a> <a id="8948" class="Symbol">{{</a><a id="8950" href="simple_essence.html#8950" class="Bound">_</a> <a id="8952" class="Symbol">:</a> <a id="8954" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="8963" href="simple_essence.html#8910" class="Bound">A</a><a id="8964" class="Symbol">}}</a>
        <a id="8975" class="Symbol">{{</a><a id="8977" href="simple_essence.html#8977" class="Bound">_</a> <a id="8979" class="Symbol">:</a> <a id="8981" href="simple_essence.html#7660" class="Record">VectorSpace</a> <a id="8993" href="simple_essence.html#8910" class="Bound">A</a><a id="8994" class="Symbol">}}</a>
        <a id="9005" class="Comment">-------------------------------------</a>
      <a id="9049" class="Symbol">→</a> <a id="9051" href="simple_essence.html#8910" class="Bound">A</a> <a id="9053" class="Symbol">→</a> <a id="9055" href="simple_essence.html#6914" class="Record">LinMap</a> <a id="9062" href="simple_essence.html#8910" class="Bound">A</a> <a id="9064" href="simple_essence.html#5988" class="Datatype">§</a>
<a id="9066" href="simple_essence.html#8901" class="Function">a⊸§←a</a> <a id="9072" class="Symbol">=</a> <a id="9074" class="Symbol">λ</a> <a id="9076" class="Symbol">{</a> <a id="9078" href="simple_essence.html#9078" class="Bound">a</a> <a id="9080" class="Symbol">→</a> <a id="9082" href="simple_essence.html#7091" class="InductiveConstructor">mkLM</a> <a id="9087" class="Symbol">(</a><a id="9088" href="simple_essence.html#9078" class="Bound">a</a> <a id="9090" href="simple_essence.html#7905" class="Field Operator">·_</a><a id="9092" class="Symbol">)</a> <a id="9094" href="simple_essence.html#7983" class="Field">·-distrib-⊕</a> <a id="9106" href="simple_essence.html#8115" class="Field">·-comm-⊛</a> <a id="9115" class="Symbol">}</a>

<a id="9118" class="Comment">-- Danger, Will Robinson!</a>
<a id="9144" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9156" href="simple_essence.html#9156" class="Postulate">x·z≡y·z→x≡y</a> <a id="9168" class="Symbol">:</a> <a id="9170" class="Symbol">{</a><a id="9171" href="simple_essence.html#9171" class="Bound">A</a> <a id="9173" class="Symbol">:</a> <a id="9175" class="PrimitiveType">Set</a> <a id="9179" href="simple_essence.html#5374" class="Bound">a</a><a id="9180" class="Symbol">}</a>
                <a id="9198" class="Symbol">{{</a><a id="9200" href="simple_essence.html#9200" class="Bound">_</a> <a id="9202" class="Symbol">:</a> <a id="9204" href="simple_essence.html#6028" class="Record">Additive</a> <a id="9213" href="simple_essence.html#9171" class="Bound">A</a><a id="9214" class="Symbol">}}</a> <a id="9217" class="Symbol">{{</a><a id="9219" href="simple_essence.html#9219" class="Bound">_</a> <a id="9221" class="Symbol">:</a> <a id="9223" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="9232" href="simple_essence.html#9171" class="Bound">A</a><a id="9233" class="Symbol">}}</a> <a id="9236" class="Symbol">{{</a><a id="9238" href="simple_essence.html#9238" class="Bound">_</a> <a id="9240" class="Symbol">:</a> <a id="9242" href="simple_essence.html#7660" class="Record">VectorSpace</a> <a id="9254" href="simple_essence.html#9171" class="Bound">A</a><a id="9255" class="Symbol">}}</a>
                <a id="9274" class="Symbol">{</a><a id="9275" href="simple_essence.html#9275" class="Bound">x</a> <a id="9277" href="simple_essence.html#9277" class="Bound">y</a> <a id="9279" class="Symbol">:</a> <a id="9281" href="simple_essence.html#9171" class="Bound">A</a><a id="9282" class="Symbol">}</a>
              <a id="9298" class="Symbol">→</a> <a id="9300" class="Symbol">(∀</a> <a id="9303" class="Symbol">{</a><a id="9304" href="simple_essence.html#9304" class="Bound">z</a> <a id="9306" class="Symbol">:</a> <a id="9308" href="simple_essence.html#9171" class="Bound">A</a><a id="9309" class="Symbol">}</a> <a id="9311" class="Symbol">→</a> <a id="9313" href="simple_essence.html#9275" class="Bound">x</a> <a id="9315" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="9317" href="simple_essence.html#9304" class="Bound">z</a> <a id="9319" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9321" href="simple_essence.html#9277" class="Bound">y</a> <a id="9323" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="9325" href="simple_essence.html#9304" class="Bound">z</a><a id="9326" class="Symbol">)</a>
                <a id="9344" class="Comment">-----------------------------------------------------------</a>
              <a id="9418" class="Symbol">→</a> <a id="9420" href="simple_essence.html#9275" class="Bound">x</a> <a id="9422" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9424" href="simple_essence.html#9277" class="Bound">y</a>
<a id="9426" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9486" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9553" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9584" href="simple_essence.html#9584" class="Function">a⊸§↔a</a> <a id="9590" class="Symbol">:</a> <a id="9592" class="Symbol">{</a><a id="9593" href="simple_essence.html#9593" class="Bound">A</a> <a id="9595" class="Symbol">:</a> <a id="9597" class="PrimitiveType">Set</a> <a id="9601" href="simple_essence.html#5374" class="Bound">a</a><a id="9602" class="Symbol">}</a>
        <a id="9612" class="Symbol">{{</a><a id="9614" href="simple_essence.html#9614" class="Bound">_</a> <a id="9616" class="Symbol">:</a> <a id="9618" href="simple_essence.html#6028" class="Record">Additive</a> <a id="9627" href="simple_essence.html#9593" class="Bound">A</a><a id="9628" class="Symbol">}}</a> <a id="9631" class="Symbol">{{</a><a id="9633" href="simple_essence.html#9633" class="Bound">_</a> <a id="9635" class="Symbol">:</a> <a id="9637" href="simple_essence.html#6642" class="Record">Scalable</a> <a id="9646" href="simple_essence.html#9593" class="Bound">A</a><a id="9647" class="Symbol">}}</a>
        <a id="9658" class="Symbol">{{</a><a id="9660" href="simple_essence.html#9660" class="Bound">_</a> <a id="9662" class="Symbol">:</a> <a id="9664" href="simple_essence.html#7660" class="Record">VectorSpace</a> <a id="9676" href="simple_essence.html#9593" class="Bound">A</a><a id="9677" class="Symbol">}}</a>
        <a id="9688" class="Comment">-------------------------------------</a>
      <a id="9732" class="Symbol">→</a> <a id="9734" class="Symbol">(</a><a id="9735" href="simple_essence.html#6914" class="Record">LinMap</a> <a id="9742" href="simple_essence.html#9593" class="Bound">A</a> <a id="9744" href="simple_essence.html#5988" class="Datatype">§</a><a id="9745" class="Symbol">)</a> <a id="9747" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9749" href="simple_essence.html#9593" class="Bound">A</a>
<a id="9751" href="simple_essence.html#9584" class="Function">a⊸§↔a</a> <a id="9757" class="Symbol">{</a><a id="9758" href="simple_essence.html#9758" class="Bound">A</a><a id="9759" class="Symbol">}</a> <a id="9761" class="Symbol">=</a>
  <a id="9765" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9769" class="Symbol">{</a><a id="9770" class="Argument">f</a> <a id="9772" class="Symbol">=</a> <a id="9774" href="simple_essence.html#8659" class="Function">a⊸§→a</a><a id="9779" class="Symbol">}</a> <a id="9781" class="Symbol">{</a><a id="9782" class="Argument">f⁻¹</a> <a id="9786" class="Symbol">=</a> <a id="9788" href="simple_essence.html#8901" class="Function">a⊸§←a</a><a id="9793" class="Symbol">}</a>
      <a id="9801" class="Symbol">(</a> <a id="9803" class="Symbol">(λ</a> <a id="9806" class="Symbol">{</a><a id="9807" href="simple_essence.html#9807" class="Bound">x</a> <a id="9809" class="Symbol">→</a> <a id="9811" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="9835" href="simple_essence.html#8659" class="Function">a⊸§→a</a> <a id="9841" class="Symbol">(</a><a id="9842" href="simple_essence.html#8901" class="Function">a⊸§←a</a> <a id="9848" href="simple_essence.html#9807" class="Bound">x</a><a id="9849" class="Symbol">)</a>
                <a id="9867" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9889" href="simple_essence.html#8659" class="Function">a⊸§→a</a> <a id="9895" class="Symbol">(</a><a id="9896" href="simple_essence.html#7091" class="InductiveConstructor">mkLM</a> <a id="9901" class="Symbol">(</a><a id="9902" href="simple_essence.html#9807" class="Bound">x</a> <a id="9904" href="simple_essence.html#7905" class="Field Operator">·_</a><a id="9906" class="Symbol">)</a> <a id="9908" href="simple_essence.html#7983" class="Field">·-distrib-⊕</a> <a id="9920" href="simple_essence.html#8115" class="Field">·-comm-⊛</a><a id="9928" class="Symbol">)</a>
                <a id="9946" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9968" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="9974" class="Symbol">(λ</a> <a id="9977" href="simple_essence.html#9977" class="Bound">acc</a> <a id="9981" href="simple_essence.html#9981" class="Bound">v</a> <a id="9983" class="Symbol">→</a> <a id="9985" href="simple_essence.html#9977" class="Bound">acc</a> <a id="9989" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="9991" class="Symbol">(</a><a id="9992" href="simple_essence.html#9807" class="Bound">x</a> <a id="9994" href="simple_essence.html#7905" class="Field Operator">·</a> <a id="9996" href="simple_essence.html#9981" class="Bound">v</a><a id="9997" class="Symbol">)</a> <a id="9999" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="10001" href="simple_essence.html#9981" class="Bound">v</a><a id="10002" class="Symbol">)</a> <a id="10004" href="simple_essence.html#6141" class="Field">id⊕</a> <a id="10008" href="simple_essence.html#7880" class="Field">basisSet</a>
                <a id="10033" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10036" href="simple_essence.html#9156" class="Postulate">x·z≡y·z→x≡y</a> <a id="10048" class="Symbol">(</a><a id="10049" href="simple_essence.html#8383" class="Field">orthonormal</a> <a id="10061" class="Symbol">{</a><a id="10062" class="Argument">f</a> <a id="10064" class="Symbol">=</a> <a id="10066" class="Symbol">(</a><a id="10067" href="simple_essence.html#9807" class="Bound">x</a> <a id="10069" href="simple_essence.html#7905" class="Field Operator">·_</a><a id="10071" class="Symbol">)})</a> <a id="10075" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10095" href="simple_essence.html#9807" class="Bound">x</a>
                <a id="10113" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10114" class="Symbol">})</a>
      <a id="10123" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10125" class="Symbol">λ</a> <a id="10127" class="Symbol">{</a><a id="10128" href="simple_essence.html#10128" class="Bound">lm</a> <a id="10131" class="Symbol">→</a> <a id="10133" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10157" href="simple_essence.html#8901" class="Function">a⊸§←a</a> <a id="10163" class="Symbol">(</a><a id="10164" href="simple_essence.html#8659" class="Function">a⊸§→a</a> <a id="10170" href="simple_essence.html#10128" class="Bound">lm</a><a id="10172" class="Symbol">)</a>
                <a id="10190" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10212" href="simple_essence.html#8901" class="Function">a⊸§←a</a> <a id="10218" class="Symbol">(</a><a id="10219" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10225" class="Symbol">(λ</a> <a id="10228" href="simple_essence.html#10228" class="Bound">acc</a> <a id="10232" href="simple_essence.html#10232" class="Bound">v</a> <a id="10234" class="Symbol">→</a> <a id="10236" href="simple_essence.html#10228" class="Bound">acc</a> <a id="10240" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="10242" class="Symbol">(</a><a id="10243" href="simple_essence.html#7108" class="Field">LinMap.f</a> <a id="10252" href="simple_essence.html#10128" class="Bound">lm</a> <a id="10255" href="simple_essence.html#10232" class="Bound">v</a><a id="10256" class="Symbol">)</a> <a id="10258" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="10260" href="simple_essence.html#10232" class="Bound">v</a><a id="10261" class="Symbol">)</a> <a id="10263" href="simple_essence.html#6141" class="Field">id⊕</a> <a id="10267" href="simple_essence.html#7880" class="Field">basisSet</a><a id="10275" class="Symbol">)</a>
                <a id="10293" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10315" href="simple_essence.html#7091" class="InductiveConstructor">mkLM</a> <a id="10320" class="Symbol">((</a><a id="10322" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10328" class="Symbol">(λ</a> <a id="10331" href="simple_essence.html#10331" class="Bound">acc</a> <a id="10335" href="simple_essence.html#10335" class="Bound">v</a> <a id="10337" class="Symbol">→</a> <a id="10339" href="simple_essence.html#10331" class="Bound">acc</a> <a id="10343" href="simple_essence.html#6154" class="Field Operator">⊕</a> <a id="10345" class="Symbol">(</a><a id="10346" href="simple_essence.html#7108" class="Field">LinMap.f</a> <a id="10355" href="simple_essence.html#10128" class="Bound">lm</a> <a id="10358" href="simple_essence.html#10335" class="Bound">v</a><a id="10359" class="Symbol">)</a> <a id="10361" href="simple_essence.html#6755" class="Field Operator">⊛</a> <a id="10363" href="simple_essence.html#10335" class="Bound">v</a><a id="10364" class="Symbol">)</a> <a id="10366" href="simple_essence.html#6141" class="Field">id⊕</a> <a id="10370" href="simple_essence.html#7880" class="Field">basisSet</a><a id="10378" class="Symbol">)</a><a id="10379" href="simple_essence.html#7905" class="Field Operator">·_</a><a id="10381" class="Symbol">)</a>
                       <a id="10406" href="simple_essence.html#7983" class="Field">·-distrib-⊕</a> <a id="10418" href="simple_essence.html#8115" class="Field">·-comm-⊛</a>
                <a id="10443" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10446" href="simple_essence.html#7426" class="Postulate">⊸≡</a> <a id="10449" class="Symbol">(</a> <a id="10451" href="simple_essence.html#5907" class="Postulate">extensionality</a>
                          <a id="10492" class="Symbol">(</a> <a id="10494" class="Symbol">λ</a> <a id="10496" href="simple_essence.html#10496" class="Bound">x</a> <a id="10498" class="Symbol">→</a> <a id="10500" href="simple_essence.html#8383" class="Field">orthonormal</a> <a id="10512" class="Symbol">{</a><a id="10513" class="Argument">f</a> <a id="10515" class="Symbol">=</a> <a id="10517" href="simple_essence.html#7108" class="Field">LinMap.f</a> <a id="10526" href="simple_essence.html#10128" class="Bound">lm</a><a id="10528" class="Symbol">}</a> <a id="10530" class="Symbol">{</a><a id="10531" class="Argument">x</a> <a id="10533" class="Symbol">=</a> <a id="10535" href="simple_essence.html#10496" class="Bound">x</a><a id="10536" class="Symbol">}</a> <a id="10538" class="Symbol">)</a>
                      <a id="10562" class="Symbol">)</a>
                 <a id="10581" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10601" href="simple_essence.html#10128" class="Bound">lm</a>
                <a id="10620" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10621" class="Symbol">}</a>
      <a id="10629" class="Symbol">)</a>

<a id="10632" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10715" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10777" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="10871" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="10934" class="Comment">--</a>
<a id="10937" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="10960" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="11009" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="11042" class="Comment">--         -------------------------------------</a>
<a id="11091" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11119" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>