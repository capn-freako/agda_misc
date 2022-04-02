---
format: 'markdown+latex'
title: 'Agda Doodlings, re: Conal`s _Simple Essence of Automatic Differentiation_'
author: 'David Banas <capn.freako@gmail.com>'
date: 2022-04-02
copy: Copyright (c) 2022 David Banas; all rights reserved World wide.
...

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

<pre class="Agda"><a id="5266" class="Keyword">module</a> <a id="5273" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5288" class="Symbol">{</a><a id="5289" href="simple_essence.html#5289" class="Bound">s</a> <a id="5291" href="simple_essence.html#5291" class="Bound">a</a> <a id="5293" href="simple_essence.html#5293" class="Bound">b</a><a id="5294" class="Symbol">}</a> <a id="5296" class="Keyword">where</a>

<a id="5303" class="Keyword">open</a> <a id="5308" class="Keyword">import</a> <a id="5315" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5334" class="Keyword">open</a> <a id="5339" class="Keyword">import</a> <a id="5346" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5381" class="Keyword">using</a> <a id="5387" class="Symbol">(</a><a id="5388" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5402" class="Symbol">)</a>
<a id="5404" class="Keyword">open</a> <a id="5409" class="Keyword">import</a> <a id="5416" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5427" class="Keyword">open</a> <a id="5432" class="Keyword">import</a> <a id="5439" href="Data.List.html" class="Module">Data.List</a>
<a id="5449" class="Keyword">open</a> <a id="5454" class="Keyword">import</a> <a id="5461" href="Function.html" class="Module">Function</a> <a id="5470" class="Keyword">using</a> <a id="5476" class="Symbol">(</a><a id="5477" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5480" class="Symbol">;</a> <a id="5482" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5485" class="Symbol">;</a> <a id="5487" href="Function.Base.html#615" class="Function">id</a><a id="5489" class="Symbol">)</a>
<a id="5491" class="Keyword">open</a> <a id="5496" class="Keyword">import</a> <a id="5503" href="Level.html" class="Module">Level</a> <a id="5509" class="Keyword">using</a> <a id="5515" class="Symbol">(</a><a id="5516" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5521" class="Symbol">;</a> <a id="5523" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5526" class="Symbol">)</a>

<a id="5529" class="Keyword">import</a> <a id="5536" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5574" class="Symbol">as</a> <a id="5577" class="Module">Eq</a>
<a id="5580" class="Keyword">open</a> <a id="5585" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5588" class="Keyword">using</a> <a id="5594" class="Symbol">(</a><a id="5595" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5598" class="Symbol">;</a> <a id="5600" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5604" class="Symbol">;</a> <a id="5606" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5611" class="Symbol">;</a> <a id="5613" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5616" class="Symbol">;</a> <a id="5618" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5622" class="Symbol">;</a> <a id="5624" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5629" class="Symbol">;</a> <a id="5631" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5639" class="Symbol">;</a> <a id="5641" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5646" class="Symbol">)</a>
<a id="5648" class="Keyword">open</a> <a id="5653" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5668" class="Keyword">using</a> <a id="5674" class="Symbol">(</a><a id="5675" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5681" class="Symbol">;</a> <a id="5683" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5688" class="Symbol">;</a> <a id="5690" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5696" class="Symbol">;</a> <a id="5698" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5700" class="Symbol">)</a>

<a id="5703" class="Keyword">postulate</a>
  <a id="5715" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="5790" href="simple_essence.html#5790" class="Postulate">id+</a> <a id="5794" class="Symbol">:</a> <a id="5796" class="Symbol">{</a><a id="5797" href="simple_essence.html#5797" class="Bound">x</a> <a id="5799" class="Symbol">:</a> <a id="5801" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="5806" class="Symbol">}</a> <a id="5808" class="Symbol">→</a> <a id="5810" class="Number">0.0</a> <a id="5814" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="5816" href="simple_essence.html#5797" class="Bound">x</a> <a id="5818" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5820" href="simple_essence.html#5797" class="Bound">x</a>
  <a id="extensionality"></a><a id="5824" href="simple_essence.html#5824" class="Postulate">extensionality</a> <a id="5839" class="Symbol">:</a> <a id="5841" class="Symbol">∀</a> <a id="5843" class="Symbol">{</a><a id="5844" href="simple_essence.html#5844" class="Bound">ℓ₁</a> <a id="5847" href="simple_essence.html#5847" class="Bound">ℓ₂</a><a id="5849" class="Symbol">}</a> <a id="5851" class="Symbol">→</a> <a id="5853" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="5868" href="simple_essence.html#5844" class="Bound">ℓ₁</a> <a id="5871" href="simple_essence.html#5847" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="5875" href="simple_essence.html#5875" class="Function">ℓ</a> <a id="5877" class="Symbol">:</a> <a id="5879" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="5885" href="simple_essence.html#5875" class="Function">ℓ</a> <a id="5887" class="Symbol">=</a> <a id="5889" href="simple_essence.html#5289" class="Bound">s</a> <a id="5891" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5893" href="simple_essence.html#5291" class="Bound">a</a> <a id="5895" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5897" href="simple_essence.html#5293" class="Bound">b</a>

<a id="5900" class="Keyword">data</a> <a id="§"></a><a id="5905" href="simple_essence.html#5905" class="Datatype">§</a> <a id="5907" class="Symbol">:</a> <a id="5909" class="PrimitiveType">Set</a> <a id="5913" href="simple_essence.html#5291" class="Bound">a</a> <a id="5915" class="Keyword">where</a>
  <a id="§.S"></a><a id="5923" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="5925" class="Symbol">:</a> <a id="5927" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="5933" class="Symbol">→</a> <a id="5935" href="simple_essence.html#5905" class="Datatype">§</a>

<a id="5938" class="Keyword">record</a> <a id="Additive"></a><a id="5945" href="simple_essence.html#5945" class="Record">Additive</a> <a id="5954" class="Symbol">(</a><a id="5955" href="simple_essence.html#5955" class="Bound">A</a> <a id="5957" class="Symbol">:</a> <a id="5959" class="PrimitiveType">Set</a> <a id="5963" href="simple_essence.html#5291" class="Bound">a</a><a id="5964" class="Symbol">)</a> <a id="5966" class="Symbol">:</a> <a id="5968" class="PrimitiveType">Set</a> <a id="5972" href="simple_essence.html#5875" class="Function">ℓ</a> <a id="5974" class="Keyword">where</a>
  <a id="5982" class="Keyword">infixl</a> <a id="5989" class="Number">6</a> <a id="5991" href="simple_essence.html#6071" class="Field Operator">_⊕_</a>  <a id="5996" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6048" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6058" href="simple_essence.html#6058" class="Field">id⊕</a>  <a id="6063" class="Symbol">:</a> <a id="6065" href="simple_essence.html#5955" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6071" href="simple_essence.html#6071" class="Field Operator">_⊕_</a>  <a id="6076" class="Symbol">:</a> <a id="6078" href="simple_essence.html#5955" class="Bound">A</a> <a id="6080" class="Symbol">→</a> <a id="6082" href="simple_essence.html#5955" class="Bound">A</a> <a id="6084" class="Symbol">→</a> <a id="6086" href="simple_essence.html#5955" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6092" href="simple_essence.html#6092" class="Field">id-⊕</a> <a id="6097" class="Symbol">:</a> <a id="6099" class="Symbol">(</a><a id="6100" href="simple_essence.html#6100" class="Bound">a</a> <a id="6102" class="Symbol">:</a> <a id="6104" href="simple_essence.html#5955" class="Bound">A</a><a id="6105" class="Symbol">)</a>
           <a id="6118" class="Comment">-----------</a>
         <a id="6139" class="Symbol">→</a> <a id="6141" href="simple_essence.html#6058" class="Field">id⊕</a> <a id="6145" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="6147" href="simple_essence.html#6100" class="Bound">a</a> <a id="6149" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6151" href="simple_essence.html#6100" class="Bound">a</a>
    <a id="6157" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6210" class="Keyword">open</a> <a id="6215" href="simple_essence.html#5945" class="Module">Additive</a> <a id="6224" class="Symbol">{{</a> <a id="6227" class="Symbol">...</a> <a id="6231" class="Symbol">}}</a>
<a id="6234" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6245" href="simple_essence.html#6245" class="Function">AdditiveScalar</a> <a id="6260" class="Symbol">:</a> <a id="6262" href="simple_essence.html#5945" class="Record">Additive</a> <a id="6271" href="simple_essence.html#5905" class="Datatype">§</a>
  <a id="6275" href="simple_essence.html#6245" class="Function">AdditiveScalar</a> <a id="6290" class="Symbol">=</a> <a id="6292" class="Keyword">record</a>
    <a id="6303" class="Symbol">{</a> <a id="6305" href="simple_essence.html#6058" class="Field">id⊕</a>  <a id="6310" class="Symbol">=</a> <a id="6312" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6314" class="Number">0.0</a>
    <a id="6322" class="Symbol">;</a> <a id="6324" href="simple_essence.html#6071" class="Field Operator">_⊕_</a>  <a id="6329" class="Symbol">=</a> <a id="6331" class="Symbol">λ</a> <a id="6333" class="Symbol">{(</a><a id="6335" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6337" href="simple_essence.html#6337" class="Bound">x</a><a id="6338" class="Symbol">)</a> <a id="6340" class="Symbol">(</a><a id="6341" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6343" href="simple_essence.html#6343" class="Bound">y</a><a id="6344" class="Symbol">)</a> <a id="6346" class="Symbol">→</a> <a id="6348" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6350" class="Symbol">(</a><a id="6351" href="simple_essence.html#6337" class="Bound">x</a> <a id="6353" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6355" href="simple_essence.html#6343" class="Bound">y</a><a id="6356" class="Symbol">)}</a>
    <a id="6363" class="Symbol">;</a> <a id="6365" href="simple_essence.html#6092" class="Field">id-⊕</a> <a id="6370" class="Symbol">=</a> <a id="6372" class="Symbol">λ</a> <a id="6374" class="Symbol">{</a> <a id="6376" class="Symbol">(</a><a id="6377" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6379" href="simple_essence.html#6379" class="Bound">x</a><a id="6380" class="Symbol">)</a> <a id="6382" class="Symbol">→</a> <a id="6384" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6417" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6419" class="Symbol">(</a><a id="6420" class="Number">0.0</a> <a id="6424" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6426" href="simple_essence.html#6379" class="Bound">x</a><a id="6427" class="Symbol">)</a>
                         <a id="6454" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6457" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6462" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6464" href="simple_essence.html#5790" class="Postulate">id+</a> <a id="6468" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6497" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6499" href="simple_essence.html#6379" class="Bound">x</a>
                         <a id="6526" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6543" class="Symbol">}</a>
    <a id="6549" class="Symbol">}</a>

<a id="6552" class="Keyword">record</a> <a id="Scalable"></a><a id="6559" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="6568" class="Symbol">(</a><a id="6569" href="simple_essence.html#6569" class="Bound">A</a> <a id="6571" class="Symbol">:</a> <a id="6573" class="PrimitiveType">Set</a> <a id="6577" href="simple_essence.html#5291" class="Bound">a</a><a id="6578" class="Symbol">)</a> <a id="6580" class="Symbol">:</a> <a id="6582" class="PrimitiveType">Set</a> <a id="6586" href="simple_essence.html#5875" class="Function">ℓ</a> <a id="6588" class="Keyword">where</a>
  <a id="6596" class="Keyword">infixl</a> <a id="6603" class="Number">7</a> <a id="6605" href="simple_essence.html#6672" class="Field Operator">_⊛_</a>  <a id="6610" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6662" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6672" href="simple_essence.html#6672" class="Field Operator">_⊛_</a> <a id="6676" class="Symbol">:</a> <a id="6678" href="simple_essence.html#5905" class="Datatype">§</a> <a id="6680" class="Symbol">→</a> <a id="6682" href="simple_essence.html#6569" class="Bound">A</a> <a id="6684" class="Symbol">→</a> <a id="6686" href="simple_essence.html#6569" class="Bound">A</a>
<a id="6688" class="Keyword">open</a> <a id="6693" href="simple_essence.html#6559" class="Module">Scalable</a> <a id="6702" class="Symbol">{{</a> <a id="6705" class="Symbol">...</a> <a id="6709" class="Symbol">}}</a>
<a id="6712" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="6723" href="simple_essence.html#6723" class="Function">ScalableScalar</a> <a id="6738" class="Symbol">:</a> <a id="6740" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="6749" href="simple_essence.html#5905" class="Datatype">§</a>
  <a id="6753" href="simple_essence.html#6723" class="Function">ScalableScalar</a> <a id="6768" class="Symbol">=</a> <a id="6770" class="Keyword">record</a>
    <a id="6781" class="Symbol">{</a> <a id="6783" href="simple_essence.html#6672" class="Field Operator">_⊛_</a> <a id="6787" class="Symbol">=</a> <a id="6789" class="Symbol">λ</a> <a id="6791" class="Symbol">{(</a><a id="6793" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6795" href="simple_essence.html#6795" class="Bound">x</a><a id="6796" class="Symbol">)</a> <a id="6798" class="Symbol">(</a><a id="6799" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6801" href="simple_essence.html#6801" class="Bound">y</a><a id="6802" class="Symbol">)</a> <a id="6804" class="Symbol">→</a> <a id="6806" href="simple_essence.html#5923" class="InductiveConstructor">S</a> <a id="6808" class="Symbol">(</a><a id="6809" href="simple_essence.html#6795" class="Bound">x</a> <a id="6811" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="6813" href="simple_essence.html#6801" class="Bound">y</a><a id="6814" class="Symbol">)}</a>
    <a id="6821" class="Symbol">}</a>

<a id="6824" class="Keyword">record</a> <a id="LinMap"></a><a id="6831" href="simple_essence.html#6831" class="Record">LinMap</a> <a id="6838" class="Symbol">(</a><a id="6839" href="simple_essence.html#6839" class="Bound">A</a> <a id="6841" class="Symbol">:</a> <a id="6843" class="PrimitiveType">Set</a> <a id="6847" href="simple_essence.html#5291" class="Bound">a</a><a id="6848" class="Symbol">)</a> <a id="6850" class="Symbol">(</a><a id="6851" href="simple_essence.html#6851" class="Bound">B</a> <a id="6853" class="Symbol">:</a> <a id="6855" class="PrimitiveType">Set</a> <a id="6859" href="simple_essence.html#5291" class="Bound">a</a><a id="6860" class="Symbol">)</a>
              <a id="6876" class="Symbol">{{</a><a id="6878" href="simple_essence.html#6878" class="Bound">_</a> <a id="6880" class="Symbol">:</a> <a id="6882" href="simple_essence.html#5945" class="Record">Additive</a> <a id="6891" href="simple_essence.html#6839" class="Bound">A</a><a id="6892" class="Symbol">}}</a> <a id="6895" class="Symbol">{{</a><a id="6897" href="simple_essence.html#6897" class="Bound">_</a> <a id="6899" class="Symbol">:</a> <a id="6901" href="simple_essence.html#5945" class="Record">Additive</a> <a id="6910" href="simple_essence.html#6851" class="Bound">B</a><a id="6911" class="Symbol">}}</a>
              <a id="6928" class="Symbol">{{</a><a id="6930" href="simple_essence.html#6930" class="Bound">_</a> <a id="6932" class="Symbol">:</a> <a id="6934" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="6943" href="simple_essence.html#6839" class="Bound">A</a><a id="6944" class="Symbol">}}</a> <a id="6947" class="Symbol">{{</a><a id="6949" href="simple_essence.html#6949" class="Bound">_</a> <a id="6951" class="Symbol">:</a> <a id="6953" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="6962" href="simple_essence.html#6851" class="Bound">B</a><a id="6963" class="Symbol">}}</a>
              <a id="6980" class="Symbol">:</a> <a id="6982" class="PrimitiveType">Set</a> <a id="6986" href="simple_essence.html#5875" class="Function">ℓ</a> <a id="6988" class="Keyword">where</a>
  <a id="6996" class="Keyword">constructor</a> <a id="mkLM"></a><a id="7008" href="simple_essence.html#7008" class="InductiveConstructor">mkLM</a>
  <a id="7015" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="7025" href="simple_essence.html#7025" class="Field">f</a>      <a id="7032" class="Symbol">:</a> <a id="7034" href="simple_essence.html#6839" class="Bound">A</a> <a id="7036" class="Symbol">→</a> <a id="7038" href="simple_essence.html#6851" class="Bound">B</a>

    <a id="LinMap.adds"></a><a id="7045" href="simple_essence.html#7045" class="Field">adds</a>   <a id="7052" class="Symbol">:</a> <a id="7054" class="Symbol">∀</a> <a id="7056" class="Symbol">{</a><a id="7057" href="simple_essence.html#7057" class="Bound">a</a> <a id="7059" href="simple_essence.html#7059" class="Bound">b</a> <a id="7061" class="Symbol">:</a> <a id="7063" href="simple_essence.html#6839" class="Bound">A</a><a id="7064" class="Symbol">}</a>
             <a id="7079" class="Comment">---------------------</a>
           <a id="7112" class="Symbol">→</a> <a id="7114" href="simple_essence.html#7025" class="Field">f</a> <a id="7116" class="Symbol">(</a><a id="7117" href="simple_essence.html#7057" class="Bound">a</a> <a id="7119" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="7121" href="simple_essence.html#7059" class="Bound">b</a><a id="7122" class="Symbol">)</a> <a id="7124" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7126" href="simple_essence.html#7025" class="Field">f</a> <a id="7128" href="simple_essence.html#7057" class="Bound">a</a> <a id="7130" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="7132" href="simple_essence.html#7025" class="Field">f</a> <a id="7134" href="simple_essence.html#7059" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7141" href="simple_essence.html#7141" class="Field">scales</a> <a id="7148" class="Symbol">:</a> <a id="7150" class="Symbol">∀</a> <a id="7152" class="Symbol">{</a><a id="7153" href="simple_essence.html#7153" class="Bound">s</a> <a id="7155" class="Symbol">:</a> <a id="7157" href="simple_essence.html#5905" class="Datatype">§</a><a id="7158" class="Symbol">}</a> <a id="7160" class="Symbol">{</a><a id="7161" href="simple_essence.html#7161" class="Bound">a</a> <a id="7163" class="Symbol">:</a> <a id="7165" href="simple_essence.html#6839" class="Bound">A</a><a id="7166" class="Symbol">}</a>
             <a id="7181" class="Comment">-------------------</a>
           <a id="7212" class="Symbol">→</a> <a id="7214" href="simple_essence.html#7025" class="Field">f</a> <a id="7216" class="Symbol">(</a><a id="7217" href="simple_essence.html#7153" class="Bound">s</a> <a id="7219" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="7221" href="simple_essence.html#7161" class="Bound">a</a><a id="7222" class="Symbol">)</a> <a id="7224" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7226" href="simple_essence.html#7153" class="Bound">s</a> <a id="7228" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="7230" href="simple_essence.html#7025" class="Field">f</a> <a id="7232" href="simple_essence.html#7161" class="Bound">a</a>
<a id="7234" class="Keyword">open</a> <a id="7239" href="simple_essence.html#6831" class="Module">LinMap</a> <a id="7246" class="Symbol">{{</a> <a id="7249" class="Symbol">...</a> <a id="7253" class="Symbol">}}</a>

<a id="7257" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7283" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7331" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7343" href="simple_essence.html#7343" class="Postulate">⊸≡</a> <a id="7346" class="Symbol">:</a> <a id="7348" class="Symbol">{</a><a id="7349" href="simple_essence.html#7349" class="Bound">A</a> <a id="7351" href="simple_essence.html#7351" class="Bound">B</a> <a id="7353" class="Symbol">:</a> <a id="7355" class="PrimitiveType">Set</a> <a id="7359" href="simple_essence.html#5291" class="Bound">a</a><a id="7360" class="Symbol">}</a>
       <a id="7369" class="Symbol">{{</a><a id="7371" href="simple_essence.html#7371" class="Bound">_</a> <a id="7373" class="Symbol">:</a> <a id="7375" href="simple_essence.html#5945" class="Record">Additive</a> <a id="7384" href="simple_essence.html#7349" class="Bound">A</a><a id="7385" class="Symbol">}}</a> <a id="7388" class="Symbol">{{</a><a id="7390" href="simple_essence.html#7390" class="Bound">_</a> <a id="7392" class="Symbol">:</a> <a id="7394" href="simple_essence.html#5945" class="Record">Additive</a> <a id="7403" href="simple_essence.html#7351" class="Bound">B</a><a id="7404" class="Symbol">}}</a>
       <a id="7414" class="Symbol">{{</a><a id="7416" href="simple_essence.html#7416" class="Bound">_</a> <a id="7418" class="Symbol">:</a> <a id="7420" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="7429" href="simple_essence.html#7349" class="Bound">A</a><a id="7430" class="Symbol">}}</a> <a id="7433" class="Symbol">{{</a><a id="7435" href="simple_essence.html#7435" class="Bound">_</a> <a id="7437" class="Symbol">:</a> <a id="7439" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="7448" href="simple_essence.html#7351" class="Bound">B</a><a id="7449" class="Symbol">}}</a>
       <a id="7459" class="Symbol">{</a><a id="7460" href="simple_essence.html#7460" class="Bound">lm₁</a> <a id="7464" href="simple_essence.html#7464" class="Bound">lm₂</a> <a id="7468" class="Symbol">:</a> <a id="7470" href="simple_essence.html#6831" class="Record">LinMap</a> <a id="7477" href="simple_essence.html#7349" class="Bound">A</a> <a id="7479" href="simple_essence.html#7351" class="Bound">B</a><a id="7480" class="Symbol">}</a>
     <a id="7487" class="Symbol">→</a> <a id="7489" href="simple_essence.html#7025" class="Field">LinMap.f</a> <a id="7498" href="simple_essence.html#7460" class="Bound">lm₁</a> <a id="7502" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7504" href="simple_essence.html#7025" class="Field">LinMap.f</a> <a id="7513" href="simple_essence.html#7464" class="Bound">lm₂</a>
       <a id="7524" class="Comment">---------------------------</a>
     <a id="7557" class="Symbol">→</a> <a id="7559" href="simple_essence.html#7460" class="Bound">lm₁</a> <a id="7563" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7565" href="simple_essence.html#7464" class="Bound">lm₂</a>

<a id="7570" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7577" href="simple_essence.html#7577" class="Record">VectorSpace</a> <a id="7589" class="Symbol">(</a><a id="7590" href="simple_essence.html#7590" class="Bound">A</a> <a id="7592" class="Symbol">:</a> <a id="7594" class="PrimitiveType">Set</a> <a id="7598" href="simple_essence.html#5291" class="Bound">a</a><a id="7599" class="Symbol">)</a>
                   <a id="7620" class="Symbol">{{</a><a id="7622" href="simple_essence.html#7622" class="Bound">_</a> <a id="7624" class="Symbol">:</a> <a id="7626" href="simple_essence.html#5945" class="Record">Additive</a> <a id="7635" href="simple_essence.html#7590" class="Bound">A</a><a id="7636" class="Symbol">}}</a> <a id="7639" class="Symbol">{{</a><a id="7641" href="simple_essence.html#7641" class="Bound">_</a> <a id="7643" class="Symbol">:</a> <a id="7645" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="7654" href="simple_essence.html#7590" class="Bound">A</a><a id="7655" class="Symbol">}}</a>
                   <a id="7677" class="Symbol">:</a> <a id="7679" class="PrimitiveType">Set</a> <a id="7683" href="simple_essence.html#5875" class="Function">ℓ</a> <a id="7685" class="Keyword">where</a>
  <a id="7693" class="Keyword">field</a>
    <a id="7703" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="7797" href="simple_essence.html#7797" class="Field">basisSet</a>    <a id="7809" class="Symbol">:</a> <a id="7811" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="7816" href="simple_essence.html#7590" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="7822" href="simple_essence.html#7822" class="Field Operator">_·_</a>         <a id="7834" class="Symbol">:</a> <a id="7836" href="simple_essence.html#7590" class="Bound">A</a> <a id="7838" class="Symbol">→</a> <a id="7840" href="simple_essence.html#7590" class="Bound">A</a> <a id="7842" class="Symbol">→</a> <a id="7844" href="simple_essence.html#5905" class="Datatype">§</a>
    <a id="7850" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="7900" href="simple_essence.html#7900" class="Field">·-distrib-⊕</a> <a id="7912" class="Symbol">:</a> <a id="7914" class="Symbol">∀</a> <a id="7916" class="Symbol">{</a><a id="7917" href="simple_essence.html#7917" class="Bound">a</a> <a id="7919" href="simple_essence.html#7919" class="Bound">b</a> <a id="7921" href="simple_essence.html#7921" class="Bound">c</a> <a id="7923" class="Symbol">:</a> <a id="7925" href="simple_essence.html#7590" class="Bound">A</a><a id="7926" class="Symbol">}</a>
                  <a id="7946" class="Comment">-------------------------------</a>
                <a id="7994" class="Symbol">→</a> <a id="7996" href="simple_essence.html#7917" class="Bound">a</a> <a id="7998" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="8000" class="Symbol">(</a><a id="8001" href="simple_essence.html#7919" class="Bound">b</a> <a id="8003" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="8005" href="simple_essence.html#7921" class="Bound">c</a><a id="8006" class="Symbol">)</a> <a id="8008" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8010" class="Symbol">(</a><a id="8011" href="simple_essence.html#7917" class="Bound">a</a> <a id="8013" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="8015" href="simple_essence.html#7919" class="Bound">b</a><a id="8016" class="Symbol">)</a> <a id="8018" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="8020" class="Symbol">(</a><a id="8021" href="simple_essence.html#7917" class="Bound">a</a> <a id="8023" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="8025" href="simple_essence.html#7921" class="Bound">c</a><a id="8026" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="8032" href="simple_essence.html#8032" class="Field">·-comm-⊛</a>    <a id="8044" class="Symbol">:</a> <a id="8046" class="Symbol">∀</a> <a id="8048" class="Symbol">{</a><a id="8049" href="simple_essence.html#8049" class="Bound">s</a> <a id="8051" class="Symbol">:</a> <a id="8053" href="simple_essence.html#5905" class="Datatype">§</a><a id="8054" class="Symbol">}</a> <a id="8056" class="Symbol">{</a><a id="8057" href="simple_essence.html#8057" class="Bound">a</a> <a id="8059" href="simple_essence.html#8059" class="Bound">b</a> <a id="8061" class="Symbol">:</a> <a id="8063" href="simple_essence.html#7590" class="Bound">A</a><a id="8064" class="Symbol">}</a>
                  <a id="8084" class="Comment">-------------------------</a>
                <a id="8126" class="Symbol">→</a> <a id="8128" href="simple_essence.html#8057" class="Bound">a</a> <a id="8130" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="8132" class="Symbol">(</a><a id="8133" href="simple_essence.html#8049" class="Bound">s</a> <a id="8135" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="8137" href="simple_essence.html#8059" class="Bound">b</a><a id="8138" class="Symbol">)</a> <a id="8140" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8142" href="simple_essence.html#8049" class="Bound">s</a> <a id="8144" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="8146" class="Symbol">(</a><a id="8147" href="simple_essence.html#8057" class="Bound">a</a> <a id="8149" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="8151" href="simple_essence.html#8059" class="Bound">b</a><a id="8152" class="Symbol">)</a>
    <a id="8158" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8242" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8300" href="simple_essence.html#8300" class="Field">orthonormal</a> <a id="8312" class="Symbol">:</a> <a id="8314" class="Symbol">∀</a> <a id="8316" class="Symbol">{</a><a id="8317" href="simple_essence.html#8317" class="Bound">f</a> <a id="8319" class="Symbol">:</a> <a id="8321" href="simple_essence.html#7590" class="Bound">A</a> <a id="8323" class="Symbol">→</a> <a id="8325" href="simple_essence.html#5905" class="Datatype">§</a><a id="8326" class="Symbol">}</a>
                <a id="8344" class="Symbol">→</a> <a id="8346" class="Symbol">{</a><a id="8347" href="simple_essence.html#8347" class="Bound">x</a> <a id="8349" class="Symbol">:</a> <a id="8351" href="simple_essence.html#7590" class="Bound">A</a><a id="8352" class="Symbol">}</a>
                  <a id="8372" class="Comment">----------------------------------------------------------</a>
                <a id="8447" class="Symbol">→</a> <a id="8449" class="Symbol">(</a><a id="8450" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8456" class="Symbol">(λ</a> <a id="8459" href="simple_essence.html#8459" class="Bound">acc</a> <a id="8463" href="simple_essence.html#8463" class="Bound">v</a> <a id="8465" class="Symbol">→</a> <a id="8467" href="simple_essence.html#8459" class="Bound">acc</a> <a id="8471" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="8473" class="Symbol">(</a><a id="8474" href="simple_essence.html#8317" class="Bound">f</a> <a id="8476" href="simple_essence.html#8463" class="Bound">v</a><a id="8477" class="Symbol">)</a> <a id="8479" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="8481" href="simple_essence.html#8463" class="Bound">v</a><a id="8482" class="Symbol">)</a> <a id="8484" href="simple_essence.html#6058" class="Field">id⊕</a> <a id="8488" href="simple_essence.html#7797" class="Field">basisSet</a><a id="8496" class="Symbol">)</a> <a id="8498" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="8500" href="simple_essence.html#8347" class="Bound">x</a> <a id="8502" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8504" href="simple_essence.html#8317" class="Bound">f</a> <a id="8506" href="simple_essence.html#8347" class="Bound">x</a>
<a id="8508" class="Keyword">open</a> <a id="8513" href="simple_essence.html#7577" class="Module">VectorSpace</a> <a id="8525" class="Symbol">{{</a> <a id="8528" class="Symbol">...</a> <a id="8532" class="Symbol">}}</a>

<a id="8536" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8576" href="simple_essence.html#8576" class="Function">a⊸§→a</a> <a id="8582" class="Symbol">:</a> <a id="8584" class="Symbol">{</a><a id="8585" href="simple_essence.html#8585" class="Bound">A</a> <a id="8587" class="Symbol">:</a> <a id="8589" class="PrimitiveType">Set</a> <a id="8593" href="simple_essence.html#5291" class="Bound">a</a><a id="8594" class="Symbol">}</a>
        <a id="8604" class="Symbol">{{</a><a id="8606" href="simple_essence.html#8606" class="Bound">_</a> <a id="8608" class="Symbol">:</a> <a id="8610" href="simple_essence.html#5945" class="Record">Additive</a> <a id="8619" href="simple_essence.html#8585" class="Bound">A</a><a id="8620" class="Symbol">}}</a> <a id="8623" class="Symbol">{{</a><a id="8625" href="simple_essence.html#8625" class="Bound">_</a> <a id="8627" class="Symbol">:</a> <a id="8629" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="8638" href="simple_essence.html#8585" class="Bound">A</a><a id="8639" class="Symbol">}}</a>
        <a id="8650" class="Symbol">{{</a><a id="8652" href="simple_essence.html#8652" class="Bound">_</a> <a id="8654" class="Symbol">:</a> <a id="8656" href="simple_essence.html#7577" class="Record">VectorSpace</a> <a id="8668" href="simple_essence.html#8585" class="Bound">A</a><a id="8669" class="Symbol">}}</a>
        <a id="8680" class="Comment">-------------------------------------</a>
      <a id="8724" class="Symbol">→</a> <a id="8726" href="simple_essence.html#6831" class="Record">LinMap</a> <a id="8733" href="simple_essence.html#8585" class="Bound">A</a> <a id="8735" href="simple_essence.html#5905" class="Datatype">§</a> <a id="8737" class="Symbol">→</a> <a id="8739" href="simple_essence.html#8585" class="Bound">A</a>
<a id="8741" href="simple_essence.html#8576" class="Function">a⊸§→a</a> <a id="8747" class="Symbol">=</a> <a id="8749" class="Symbol">λ</a> <a id="8751" class="Symbol">{</a> <a id="8753" href="simple_essence.html#8753" class="Bound">lm</a> <a id="8756" class="Symbol">→</a> <a id="8758" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8764" class="Symbol">(λ</a> <a id="8767" href="simple_essence.html#8767" class="Bound">acc</a> <a id="8771" href="simple_essence.html#8771" class="Bound">v</a> <a id="8773" class="Symbol">→</a> <a id="8775" href="simple_essence.html#8767" class="Bound">acc</a> <a id="8779" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="8781" class="Symbol">(</a><a id="8782" href="simple_essence.html#7025" class="Field">LinMap.f</a> <a id="8791" href="simple_essence.html#8753" class="Bound">lm</a> <a id="8794" href="simple_essence.html#8771" class="Bound">v</a><a id="8795" class="Symbol">)</a> <a id="8797" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="8799" href="simple_essence.html#8771" class="Bound">v</a><a id="8800" class="Symbol">)</a> <a id="8802" href="simple_essence.html#6058" class="Field">id⊕</a> <a id="8806" href="simple_essence.html#7797" class="Field">basisSet</a> <a id="8815" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="8818" href="simple_essence.html#8818" class="Function">a⊸§←a</a> <a id="8824" class="Symbol">:</a> <a id="8826" class="Symbol">{</a><a id="8827" href="simple_essence.html#8827" class="Bound">A</a> <a id="8829" class="Symbol">:</a> <a id="8831" class="PrimitiveType">Set</a> <a id="8835" href="simple_essence.html#5291" class="Bound">a</a><a id="8836" class="Symbol">}</a>
        <a id="8846" class="Symbol">{{</a><a id="8848" href="simple_essence.html#8848" class="Bound">_</a> <a id="8850" class="Symbol">:</a> <a id="8852" href="simple_essence.html#5945" class="Record">Additive</a> <a id="8861" href="simple_essence.html#8827" class="Bound">A</a><a id="8862" class="Symbol">}}</a> <a id="8865" class="Symbol">{{</a><a id="8867" href="simple_essence.html#8867" class="Bound">_</a> <a id="8869" class="Symbol">:</a> <a id="8871" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="8880" href="simple_essence.html#8827" class="Bound">A</a><a id="8881" class="Symbol">}}</a>
        <a id="8892" class="Symbol">{{</a><a id="8894" href="simple_essence.html#8894" class="Bound">_</a> <a id="8896" class="Symbol">:</a> <a id="8898" href="simple_essence.html#7577" class="Record">VectorSpace</a> <a id="8910" href="simple_essence.html#8827" class="Bound">A</a><a id="8911" class="Symbol">}}</a>
        <a id="8922" class="Comment">-------------------------------------</a>
      <a id="8966" class="Symbol">→</a> <a id="8968" href="simple_essence.html#8827" class="Bound">A</a> <a id="8970" class="Symbol">→</a> <a id="8972" href="simple_essence.html#6831" class="Record">LinMap</a> <a id="8979" href="simple_essence.html#8827" class="Bound">A</a> <a id="8981" href="simple_essence.html#5905" class="Datatype">§</a>
<a id="8983" href="simple_essence.html#8818" class="Function">a⊸§←a</a> <a id="8989" class="Symbol">=</a> <a id="8991" class="Symbol">λ</a> <a id="8993" class="Symbol">{</a> <a id="8995" href="simple_essence.html#8995" class="Bound">a</a> <a id="8997" class="Symbol">→</a> <a id="8999" href="simple_essence.html#7008" class="InductiveConstructor">mkLM</a> <a id="9004" class="Symbol">(</a><a id="9005" href="simple_essence.html#8995" class="Bound">a</a> <a id="9007" href="simple_essence.html#7822" class="Field Operator">·_</a><a id="9009" class="Symbol">)</a> <a id="9011" href="simple_essence.html#7900" class="Field">·-distrib-⊕</a> <a id="9023" href="simple_essence.html#8032" class="Field">·-comm-⊛</a> <a id="9032" class="Symbol">}</a>

<a id="9035" class="Comment">-- Danger, Will Robinson!</a>
<a id="9061" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9073" href="simple_essence.html#9073" class="Postulate">x·z≡y·z→x≡y</a> <a id="9085" class="Symbol">:</a> <a id="9087" class="Symbol">{</a><a id="9088" href="simple_essence.html#9088" class="Bound">A</a> <a id="9090" class="Symbol">:</a> <a id="9092" class="PrimitiveType">Set</a> <a id="9096" href="simple_essence.html#5291" class="Bound">a</a><a id="9097" class="Symbol">}</a>
                <a id="9115" class="Symbol">{{</a><a id="9117" href="simple_essence.html#9117" class="Bound">_</a> <a id="9119" class="Symbol">:</a> <a id="9121" href="simple_essence.html#5945" class="Record">Additive</a> <a id="9130" href="simple_essence.html#9088" class="Bound">A</a><a id="9131" class="Symbol">}}</a> <a id="9134" class="Symbol">{{</a><a id="9136" href="simple_essence.html#9136" class="Bound">_</a> <a id="9138" class="Symbol">:</a> <a id="9140" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="9149" href="simple_essence.html#9088" class="Bound">A</a><a id="9150" class="Symbol">}}</a> <a id="9153" class="Symbol">{{</a><a id="9155" href="simple_essence.html#9155" class="Bound">_</a> <a id="9157" class="Symbol">:</a> <a id="9159" href="simple_essence.html#7577" class="Record">VectorSpace</a> <a id="9171" href="simple_essence.html#9088" class="Bound">A</a><a id="9172" class="Symbol">}}</a>
                <a id="9191" class="Symbol">{</a><a id="9192" href="simple_essence.html#9192" class="Bound">x</a> <a id="9194" href="simple_essence.html#9194" class="Bound">y</a> <a id="9196" class="Symbol">:</a> <a id="9198" href="simple_essence.html#9088" class="Bound">A</a><a id="9199" class="Symbol">}</a>
              <a id="9215" class="Symbol">→</a> <a id="9217" class="Symbol">(∀</a> <a id="9220" class="Symbol">{</a><a id="9221" href="simple_essence.html#9221" class="Bound">z</a> <a id="9223" class="Symbol">:</a> <a id="9225" href="simple_essence.html#9088" class="Bound">A</a><a id="9226" class="Symbol">}</a> <a id="9228" class="Symbol">→</a> <a id="9230" href="simple_essence.html#9192" class="Bound">x</a> <a id="9232" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="9234" href="simple_essence.html#9221" class="Bound">z</a> <a id="9236" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9238" href="simple_essence.html#9194" class="Bound">y</a> <a id="9240" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="9242" href="simple_essence.html#9221" class="Bound">z</a><a id="9243" class="Symbol">)</a>
                <a id="9261" class="Comment">-----------------------------------------------------------</a>
              <a id="9335" class="Symbol">→</a> <a id="9337" href="simple_essence.html#9192" class="Bound">x</a> <a id="9339" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9341" href="simple_essence.html#9194" class="Bound">y</a>
<a id="9343" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9403" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9470" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9501" href="simple_essence.html#9501" class="Function">a⊸§↔a</a> <a id="9507" class="Symbol">:</a> <a id="9509" class="Symbol">{</a><a id="9510" href="simple_essence.html#9510" class="Bound">A</a> <a id="9512" class="Symbol">:</a> <a id="9514" class="PrimitiveType">Set</a> <a id="9518" href="simple_essence.html#5291" class="Bound">a</a><a id="9519" class="Symbol">}</a>
        <a id="9529" class="Symbol">{{</a><a id="9531" href="simple_essence.html#9531" class="Bound">_</a> <a id="9533" class="Symbol">:</a> <a id="9535" href="simple_essence.html#5945" class="Record">Additive</a> <a id="9544" href="simple_essence.html#9510" class="Bound">A</a><a id="9545" class="Symbol">}}</a> <a id="9548" class="Symbol">{{</a><a id="9550" href="simple_essence.html#9550" class="Bound">_</a> <a id="9552" class="Symbol">:</a> <a id="9554" href="simple_essence.html#6559" class="Record">Scalable</a> <a id="9563" href="simple_essence.html#9510" class="Bound">A</a><a id="9564" class="Symbol">}}</a>
        <a id="9575" class="Symbol">{{</a><a id="9577" href="simple_essence.html#9577" class="Bound">_</a> <a id="9579" class="Symbol">:</a> <a id="9581" href="simple_essence.html#7577" class="Record">VectorSpace</a> <a id="9593" href="simple_essence.html#9510" class="Bound">A</a><a id="9594" class="Symbol">}}</a>
        <a id="9605" class="Comment">-------------------------------------</a>
      <a id="9649" class="Symbol">→</a> <a id="9651" class="Symbol">(</a><a id="9652" href="simple_essence.html#6831" class="Record">LinMap</a> <a id="9659" href="simple_essence.html#9510" class="Bound">A</a> <a id="9661" href="simple_essence.html#5905" class="Datatype">§</a><a id="9662" class="Symbol">)</a> <a id="9664" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9666" href="simple_essence.html#9510" class="Bound">A</a>
<a id="9668" href="simple_essence.html#9501" class="Function">a⊸§↔a</a> <a id="9674" class="Symbol">{</a><a id="9675" href="simple_essence.html#9675" class="Bound">A</a><a id="9676" class="Symbol">}</a> <a id="9678" class="Symbol">=</a>
  <a id="9682" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9686" class="Symbol">{</a><a id="9687" class="Argument">f</a> <a id="9689" class="Symbol">=</a> <a id="9691" href="simple_essence.html#8576" class="Function">a⊸§→a</a><a id="9696" class="Symbol">}</a> <a id="9698" class="Symbol">{</a><a id="9699" class="Argument">f⁻¹</a> <a id="9703" class="Symbol">=</a> <a id="9705" href="simple_essence.html#8818" class="Function">a⊸§←a</a><a id="9710" class="Symbol">}</a>
      <a id="9718" class="Symbol">(</a> <a id="9720" class="Symbol">(λ</a> <a id="9723" class="Symbol">{</a><a id="9724" href="simple_essence.html#9724" class="Bound">x</a> <a id="9726" class="Symbol">→</a> <a id="9728" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="9752" href="simple_essence.html#8576" class="Function">a⊸§→a</a> <a id="9758" class="Symbol">(</a><a id="9759" href="simple_essence.html#8818" class="Function">a⊸§←a</a> <a id="9765" href="simple_essence.html#9724" class="Bound">x</a><a id="9766" class="Symbol">)</a>
                <a id="9784" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9806" href="simple_essence.html#8576" class="Function">a⊸§→a</a> <a id="9812" class="Symbol">(</a><a id="9813" href="simple_essence.html#7008" class="InductiveConstructor">mkLM</a> <a id="9818" class="Symbol">(</a><a id="9819" href="simple_essence.html#9724" class="Bound">x</a> <a id="9821" href="simple_essence.html#7822" class="Field Operator">·_</a><a id="9823" class="Symbol">)</a> <a id="9825" href="simple_essence.html#7900" class="Field">·-distrib-⊕</a> <a id="9837" href="simple_essence.html#8032" class="Field">·-comm-⊛</a><a id="9845" class="Symbol">)</a>
                <a id="9863" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9885" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="9891" class="Symbol">(λ</a> <a id="9894" href="simple_essence.html#9894" class="Bound">acc</a> <a id="9898" href="simple_essence.html#9898" class="Bound">v</a> <a id="9900" class="Symbol">→</a> <a id="9902" href="simple_essence.html#9894" class="Bound">acc</a> <a id="9906" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="9908" class="Symbol">(</a><a id="9909" href="simple_essence.html#9724" class="Bound">x</a> <a id="9911" href="simple_essence.html#7822" class="Field Operator">·</a> <a id="9913" href="simple_essence.html#9898" class="Bound">v</a><a id="9914" class="Symbol">)</a> <a id="9916" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="9918" href="simple_essence.html#9898" class="Bound">v</a><a id="9919" class="Symbol">)</a> <a id="9921" href="simple_essence.html#6058" class="Field">id⊕</a> <a id="9925" href="simple_essence.html#7797" class="Field">basisSet</a>
                <a id="9950" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="9953" href="simple_essence.html#9073" class="Postulate">x·z≡y·z→x≡y</a> <a id="9965" class="Symbol">(</a><a id="9966" href="simple_essence.html#8300" class="Field">orthonormal</a> <a id="9978" class="Symbol">{</a><a id="9979" class="Argument">f</a> <a id="9981" class="Symbol">=</a> <a id="9983" class="Symbol">(</a><a id="9984" href="simple_essence.html#9724" class="Bound">x</a> <a id="9986" href="simple_essence.html#7822" class="Field Operator">·_</a><a id="9988" class="Symbol">)})</a> <a id="9992" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10012" href="simple_essence.html#9724" class="Bound">x</a>
                <a id="10030" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10031" class="Symbol">})</a>
      <a id="10040" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10042" class="Symbol">λ</a> <a id="10044" class="Symbol">{</a><a id="10045" href="simple_essence.html#10045" class="Bound">lm</a> <a id="10048" class="Symbol">→</a> <a id="10050" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10074" href="simple_essence.html#8818" class="Function">a⊸§←a</a> <a id="10080" class="Symbol">(</a><a id="10081" href="simple_essence.html#8576" class="Function">a⊸§→a</a> <a id="10087" href="simple_essence.html#10045" class="Bound">lm</a><a id="10089" class="Symbol">)</a>
                <a id="10107" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10129" href="simple_essence.html#8818" class="Function">a⊸§←a</a> <a id="10135" class="Symbol">(</a><a id="10136" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10142" class="Symbol">(λ</a> <a id="10145" href="simple_essence.html#10145" class="Bound">acc</a> <a id="10149" href="simple_essence.html#10149" class="Bound">v</a> <a id="10151" class="Symbol">→</a> <a id="10153" href="simple_essence.html#10145" class="Bound">acc</a> <a id="10157" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="10159" class="Symbol">(</a><a id="10160" href="simple_essence.html#7025" class="Field">LinMap.f</a> <a id="10169" href="simple_essence.html#10045" class="Bound">lm</a> <a id="10172" href="simple_essence.html#10149" class="Bound">v</a><a id="10173" class="Symbol">)</a> <a id="10175" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="10177" href="simple_essence.html#10149" class="Bound">v</a><a id="10178" class="Symbol">)</a> <a id="10180" href="simple_essence.html#6058" class="Field">id⊕</a> <a id="10184" href="simple_essence.html#7797" class="Field">basisSet</a><a id="10192" class="Symbol">)</a>
                <a id="10210" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10232" href="simple_essence.html#7008" class="InductiveConstructor">mkLM</a> <a id="10237" class="Symbol">((</a><a id="10239" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10245" class="Symbol">(λ</a> <a id="10248" href="simple_essence.html#10248" class="Bound">acc</a> <a id="10252" href="simple_essence.html#10252" class="Bound">v</a> <a id="10254" class="Symbol">→</a> <a id="10256" href="simple_essence.html#10248" class="Bound">acc</a> <a id="10260" href="simple_essence.html#6071" class="Field Operator">⊕</a> <a id="10262" class="Symbol">(</a><a id="10263" href="simple_essence.html#7025" class="Field">LinMap.f</a> <a id="10272" href="simple_essence.html#10045" class="Bound">lm</a> <a id="10275" href="simple_essence.html#10252" class="Bound">v</a><a id="10276" class="Symbol">)</a> <a id="10278" href="simple_essence.html#6672" class="Field Operator">⊛</a> <a id="10280" href="simple_essence.html#10252" class="Bound">v</a><a id="10281" class="Symbol">)</a> <a id="10283" href="simple_essence.html#6058" class="Field">id⊕</a> <a id="10287" href="simple_essence.html#7797" class="Field">basisSet</a><a id="10295" class="Symbol">)</a><a id="10296" href="simple_essence.html#7822" class="Field Operator">·_</a><a id="10298" class="Symbol">)</a>
                       <a id="10323" href="simple_essence.html#7900" class="Field">·-distrib-⊕</a> <a id="10335" href="simple_essence.html#8032" class="Field">·-comm-⊛</a>
                <a id="10360" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10363" href="simple_essence.html#7343" class="Postulate">⊸≡</a> <a id="10366" class="Symbol">(</a> <a id="10368" href="simple_essence.html#5824" class="Postulate">extensionality</a>
                          <a id="10409" class="Symbol">(</a> <a id="10411" class="Symbol">λ</a> <a id="10413" href="simple_essence.html#10413" class="Bound">x</a> <a id="10415" class="Symbol">→</a> <a id="10417" href="simple_essence.html#8300" class="Field">orthonormal</a> <a id="10429" class="Symbol">{</a><a id="10430" class="Argument">f</a> <a id="10432" class="Symbol">=</a> <a id="10434" href="simple_essence.html#7025" class="Field">LinMap.f</a> <a id="10443" href="simple_essence.html#10045" class="Bound">lm</a><a id="10445" class="Symbol">}</a> <a id="10447" class="Symbol">{</a><a id="10448" class="Argument">x</a> <a id="10450" class="Symbol">=</a> <a id="10452" href="simple_essence.html#10413" class="Bound">x</a><a id="10453" class="Symbol">}</a> <a id="10455" class="Symbol">)</a>
                      <a id="10479" class="Symbol">)</a>
                 <a id="10498" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10518" href="simple_essence.html#10045" class="Bound">lm</a>
                <a id="10537" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10538" class="Symbol">}</a>
      <a id="10546" class="Symbol">)</a>

<a id="10549" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10632" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10694" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="10788" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="10851" class="Comment">--</a>
<a id="10854" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="10877" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="10926" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="10959" class="Comment">--         -------------------------------------</a>
<a id="11008" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11036" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>