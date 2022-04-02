---
format: markdown
title: 'Agda Doodlings, re: Conal`s _Simple Essence of Automatic Differentiation_'
...

# Agda Doodlings, re: Conal's "Simple Essence of Automatic Differentiation"

by: David Banas <capn.freako@gmail.com>  
on: April 1, 2022

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

<pre class="Agda"><a id="5228" class="Keyword">module</a> <a id="5235" href="simple_essence.html" class="Module Operator">simple_essence</a> <a id="5250" class="Symbol">{</a><a id="5251" href="simple_essence.html#5251" class="Bound">s</a> <a id="5253" href="simple_essence.html#5253" class="Bound">a</a> <a id="5255" href="simple_essence.html#5255" class="Bound">b</a><a id="5256" class="Symbol">}</a> <a id="5258" class="Keyword">where</a>

<a id="5265" class="Keyword">open</a> <a id="5270" class="Keyword">import</a> <a id="5277" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>
<a id="5296" class="Keyword">open</a> <a id="5301" class="Keyword">import</a> <a id="5308" href="Axiom.Extensionality.Propositional.html" class="Module">Axiom.Extensionality.Propositional</a> <a id="5343" class="Keyword">using</a> <a id="5349" class="Symbol">(</a><a id="5350" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a><a id="5364" class="Symbol">)</a>
<a id="5366" class="Keyword">open</a> <a id="5371" class="Keyword">import</a> <a id="5378" href="Data.Float.html" class="Module">Data.Float</a>
<a id="5389" class="Keyword">open</a> <a id="5394" class="Keyword">import</a> <a id="5401" href="Data.List.html" class="Module">Data.List</a>
<a id="5411" class="Keyword">open</a> <a id="5416" class="Keyword">import</a> <a id="5423" href="Function.html" class="Module">Function</a> <a id="5432" class="Keyword">using</a> <a id="5438" class="Symbol">(</a><a id="5439" href="Function.Bundles.html#7902" class="Function Operator">_↔_</a><a id="5442" class="Symbol">;</a> <a id="5444" href="Function.Bundles.html#9488" class="Function">mk↔</a><a id="5447" class="Symbol">;</a> <a id="5449" href="Function.Base.html#615" class="Function">id</a><a id="5451" class="Symbol">)</a>
<a id="5453" class="Keyword">open</a> <a id="5458" class="Keyword">import</a> <a id="5465" href="Level.html" class="Module">Level</a> <a id="5471" class="Keyword">using</a> <a id="5477" class="Symbol">(</a><a id="5478" href="Agda.Primitive.html#423" class="Postulate">Level</a><a id="5483" class="Symbol">;</a> <a id="5485" href="Agda.Primitive.html#636" class="Primitive Operator">_⊔_</a><a id="5488" class="Symbol">)</a>

<a id="5491" class="Keyword">import</a> <a id="5498" href="Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="5536" class="Symbol">as</a> <a id="5539" class="Module">Eq</a>
<a id="5542" class="Keyword">open</a> <a id="5547" href="Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="5550" class="Keyword">using</a> <a id="5556" class="Symbol">(</a><a id="5557" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">_≡_</a><a id="5560" class="Symbol">;</a> <a id="5562" href="Agda.Builtin.Equality.html#208" class="InductiveConstructor">refl</a><a id="5566" class="Symbol">;</a> <a id="5568" href="Relation.Binary.PropositionalEquality.Core.html#1025" class="Function">trans</a><a id="5573" class="Symbol">;</a> <a id="5575" href="Relation.Binary.PropositionalEquality.Core.html#980" class="Function">sym</a><a id="5578" class="Symbol">;</a> <a id="5580" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a><a id="5584" class="Symbol">;</a> <a id="5586" href="Relation.Binary.PropositionalEquality.html#1524" class="Function">cong₂</a><a id="5591" class="Symbol">;</a> <a id="5593" href="Relation.Binary.PropositionalEquality.html#1396" class="Function">cong-app</a><a id="5601" class="Symbol">;</a> <a id="5603" href="Relation.Binary.PropositionalEquality.Core.html#1076" class="Function">subst</a><a id="5608" class="Symbol">)</a>
<a id="5610" class="Keyword">open</a> <a id="5615" href="Relation.Binary.PropositionalEquality.Core.html#2419" class="Module">Eq.≡-Reasoning</a> <a id="5630" class="Keyword">using</a> <a id="5636" class="Symbol">(</a><a id="5637" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin_</a><a id="5643" class="Symbol">;</a> <a id="5645" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">_≡⟨⟩_</a><a id="5650" class="Symbol">;</a> <a id="5652" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">step-≡</a><a id="5658" class="Symbol">;</a> <a id="5660" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">_∎</a><a id="5662" class="Symbol">)</a>

<a id="5665" class="Keyword">postulate</a>
  <a id="5677" class="Comment">-- This one seems completely safe. Why isn&#39;t it in the standard library?</a>
  <a id="id+"></a><a id="5752" href="simple_essence.html#5752" class="Postulate">id+</a> <a id="5756" class="Symbol">:</a> <a id="5758" class="Symbol">{</a><a id="5759" href="simple_essence.html#5759" class="Bound">x</a> <a id="5761" class="Symbol">:</a> <a id="5763" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a><a id="5768" class="Symbol">}</a> <a id="5770" class="Symbol">→</a> <a id="5772" class="Number">0.0</a> <a id="5776" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="5778" href="simple_essence.html#5759" class="Bound">x</a> <a id="5780" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="5782" href="simple_essence.html#5759" class="Bound">x</a>
  <a id="extensionality"></a><a id="5786" href="simple_essence.html#5786" class="Postulate">extensionality</a> <a id="5801" class="Symbol">:</a> <a id="5803" class="Symbol">∀</a> <a id="5805" class="Symbol">{</a><a id="5806" href="simple_essence.html#5806" class="Bound">ℓ₁</a> <a id="5809" href="simple_essence.html#5809" class="Bound">ℓ₂</a><a id="5811" class="Symbol">}</a> <a id="5813" class="Symbol">→</a> <a id="5815" href="Axiom.Extensionality.Propositional.html#741" class="Function">Extensionality</a> <a id="5830" href="simple_essence.html#5806" class="Bound">ℓ₁</a> <a id="5833" href="simple_essence.html#5809" class="Bound">ℓ₂</a>

<a id="ℓ"></a><a id="5837" href="simple_essence.html#5837" class="Function">ℓ</a> <a id="5839" class="Symbol">:</a> <a id="5841" href="Agda.Primitive.html#423" class="Postulate">Level</a>
<a id="5847" href="simple_essence.html#5837" class="Function">ℓ</a> <a id="5849" class="Symbol">=</a> <a id="5851" href="simple_essence.html#5251" class="Bound">s</a> <a id="5853" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5855" href="simple_essence.html#5253" class="Bound">a</a> <a id="5857" href="Agda.Primitive.html#636" class="Primitive Operator">⊔</a> <a id="5859" href="simple_essence.html#5255" class="Bound">b</a>

<a id="5862" class="Keyword">data</a> <a id="§"></a><a id="5867" href="simple_essence.html#5867" class="Datatype">§</a> <a id="5869" class="Symbol">:</a> <a id="5871" class="PrimitiveType">Set</a> <a id="5875" href="simple_essence.html#5253" class="Bound">a</a> <a id="5877" class="Keyword">where</a>
  <a id="§.S"></a><a id="5885" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="5887" class="Symbol">:</a> <a id="5889" href="Agda.Builtin.Float.html#292" class="Postulate">Float</a> <a id="5895" class="Symbol">→</a> <a id="5897" href="simple_essence.html#5867" class="Datatype">§</a>

<a id="5900" class="Keyword">record</a> <a id="Additive"></a><a id="5907" href="simple_essence.html#5907" class="Record">Additive</a> <a id="5916" class="Symbol">(</a><a id="5917" href="simple_essence.html#5917" class="Bound">A</a> <a id="5919" class="Symbol">:</a> <a id="5921" class="PrimitiveType">Set</a> <a id="5925" href="simple_essence.html#5253" class="Bound">a</a><a id="5926" class="Symbol">)</a> <a id="5928" class="Symbol">:</a> <a id="5930" class="PrimitiveType">Set</a> <a id="5934" href="simple_essence.html#5837" class="Function">ℓ</a> <a id="5936" class="Keyword">where</a>
  <a id="5944" class="Keyword">infixl</a> <a id="5951" class="Number">6</a> <a id="5953" href="simple_essence.html#6033" class="Field Operator">_⊕_</a>  <a id="5958" class="Comment">-- Just matching associativity/priority of `_+_`.</a>
  <a id="6010" class="Keyword">field</a>
    <a id="Additive.id⊕"></a><a id="6020" href="simple_essence.html#6020" class="Field">id⊕</a>  <a id="6025" class="Symbol">:</a> <a id="6027" href="simple_essence.html#5917" class="Bound">A</a>
    <a id="Additive._⊕_"></a><a id="6033" href="simple_essence.html#6033" class="Field Operator">_⊕_</a>  <a id="6038" class="Symbol">:</a> <a id="6040" href="simple_essence.html#5917" class="Bound">A</a> <a id="6042" class="Symbol">→</a> <a id="6044" href="simple_essence.html#5917" class="Bound">A</a> <a id="6046" class="Symbol">→</a> <a id="6048" href="simple_essence.html#5917" class="Bound">A</a>
    <a id="Additive.id-⊕"></a><a id="6054" href="simple_essence.html#6054" class="Field">id-⊕</a> <a id="6059" class="Symbol">:</a> <a id="6061" class="Symbol">(</a><a id="6062" href="simple_essence.html#6062" class="Bound">a</a> <a id="6064" class="Symbol">:</a> <a id="6066" href="simple_essence.html#5917" class="Bound">A</a><a id="6067" class="Symbol">)</a>
           <a id="6080" class="Comment">-----------</a>
         <a id="6101" class="Symbol">→</a> <a id="6103" href="simple_essence.html#6020" class="Field">id⊕</a> <a id="6107" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="6109" href="simple_essence.html#6062" class="Bound">a</a> <a id="6111" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="6113" href="simple_essence.html#6062" class="Bound">a</a>
    <a id="6119" class="Comment">-- assoc-⊕ : (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)</a>
<a id="6172" class="Keyword">open</a> <a id="6177" href="simple_essence.html#5907" class="Module">Additive</a> <a id="6186" class="Symbol">{{</a> <a id="6189" class="Symbol">...</a> <a id="6193" class="Symbol">}}</a>
<a id="6196" class="Keyword">instance</a>
  <a id="AdditiveScalar"></a><a id="6207" href="simple_essence.html#6207" class="Function">AdditiveScalar</a> <a id="6222" class="Symbol">:</a> <a id="6224" href="simple_essence.html#5907" class="Record">Additive</a> <a id="6233" href="simple_essence.html#5867" class="Datatype">§</a>
  <a id="6237" href="simple_essence.html#6207" class="Function">AdditiveScalar</a> <a id="6252" class="Symbol">=</a> <a id="6254" class="Keyword">record</a>
    <a id="6265" class="Symbol">{</a> <a id="6267" href="simple_essence.html#6020" class="Field">id⊕</a>  <a id="6272" class="Symbol">=</a> <a id="6274" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6276" class="Number">0.0</a>
    <a id="6284" class="Symbol">;</a> <a id="6286" href="simple_essence.html#6033" class="Field Operator">_⊕_</a>  <a id="6291" class="Symbol">=</a> <a id="6293" class="Symbol">λ</a> <a id="6295" class="Symbol">{(</a><a id="6297" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6299" href="simple_essence.html#6299" class="Bound">x</a><a id="6300" class="Symbol">)</a> <a id="6302" class="Symbol">(</a><a id="6303" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6305" href="simple_essence.html#6305" class="Bound">y</a><a id="6306" class="Symbol">)</a> <a id="6308" class="Symbol">→</a> <a id="6310" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6312" class="Symbol">(</a><a id="6313" href="simple_essence.html#6299" class="Bound">x</a> <a id="6315" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6317" href="simple_essence.html#6305" class="Bound">y</a><a id="6318" class="Symbol">)}</a>
    <a id="6325" class="Symbol">;</a> <a id="6327" href="simple_essence.html#6054" class="Field">id-⊕</a> <a id="6332" class="Symbol">=</a> <a id="6334" class="Symbol">λ</a> <a id="6336" class="Symbol">{</a> <a id="6338" class="Symbol">(</a><a id="6339" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6341" href="simple_essence.html#6341" class="Bound">x</a><a id="6342" class="Symbol">)</a> <a id="6344" class="Symbol">→</a> <a id="6346" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                           <a id="6379" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6381" class="Symbol">(</a><a id="6382" class="Number">0.0</a> <a id="6386" href="Agda.Builtin.Float.html#606" class="Primitive Operator">+</a> <a id="6388" href="simple_essence.html#6341" class="Bound">x</a><a id="6389" class="Symbol">)</a>
                         <a id="6416" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="6419" href="Relation.Binary.PropositionalEquality.Core.html#1131" class="Function">cong</a> <a id="6424" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6426" href="simple_essence.html#5752" class="Postulate">id+</a> <a id="6430" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                           <a id="6459" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6461" href="simple_essence.html#6341" class="Bound">x</a>
                         <a id="6488" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a>
               <a id="6505" class="Symbol">}</a>
    <a id="6511" class="Symbol">}</a>

<a id="6514" class="Keyword">record</a> <a id="Scalable"></a><a id="6521" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="6530" class="Symbol">(</a><a id="6531" href="simple_essence.html#6531" class="Bound">A</a> <a id="6533" class="Symbol">:</a> <a id="6535" class="PrimitiveType">Set</a> <a id="6539" href="simple_essence.html#5253" class="Bound">a</a><a id="6540" class="Symbol">)</a> <a id="6542" class="Symbol">:</a> <a id="6544" class="PrimitiveType">Set</a> <a id="6548" href="simple_essence.html#5837" class="Function">ℓ</a> <a id="6550" class="Keyword">where</a>
  <a id="6558" class="Keyword">infixl</a> <a id="6565" class="Number">7</a> <a id="6567" href="simple_essence.html#6634" class="Field Operator">_⊛_</a>  <a id="6572" class="Comment">-- Just matching associativity/priority of `_*_`.</a>
  <a id="6624" class="Keyword">field</a>
    <a id="Scalable._⊛_"></a><a id="6634" href="simple_essence.html#6634" class="Field Operator">_⊛_</a> <a id="6638" class="Symbol">:</a> <a id="6640" href="simple_essence.html#5867" class="Datatype">§</a> <a id="6642" class="Symbol">→</a> <a id="6644" href="simple_essence.html#6531" class="Bound">A</a> <a id="6646" class="Symbol">→</a> <a id="6648" href="simple_essence.html#6531" class="Bound">A</a>
<a id="6650" class="Keyword">open</a> <a id="6655" href="simple_essence.html#6521" class="Module">Scalable</a> <a id="6664" class="Symbol">{{</a> <a id="6667" class="Symbol">...</a> <a id="6671" class="Symbol">}}</a>
<a id="6674" class="Keyword">instance</a>
  <a id="ScalableScalar"></a><a id="6685" href="simple_essence.html#6685" class="Function">ScalableScalar</a> <a id="6700" class="Symbol">:</a> <a id="6702" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="6711" href="simple_essence.html#5867" class="Datatype">§</a>
  <a id="6715" href="simple_essence.html#6685" class="Function">ScalableScalar</a> <a id="6730" class="Symbol">=</a> <a id="6732" class="Keyword">record</a>
    <a id="6743" class="Symbol">{</a> <a id="6745" href="simple_essence.html#6634" class="Field Operator">_⊛_</a> <a id="6749" class="Symbol">=</a> <a id="6751" class="Symbol">λ</a> <a id="6753" class="Symbol">{(</a><a id="6755" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6757" href="simple_essence.html#6757" class="Bound">x</a><a id="6758" class="Symbol">)</a> <a id="6760" class="Symbol">(</a><a id="6761" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6763" href="simple_essence.html#6763" class="Bound">y</a><a id="6764" class="Symbol">)</a> <a id="6766" class="Symbol">→</a> <a id="6768" href="simple_essence.html#5885" class="InductiveConstructor">S</a> <a id="6770" class="Symbol">(</a><a id="6771" href="simple_essence.html#6757" class="Bound">x</a> <a id="6773" href="Agda.Builtin.Float.html#694" class="Primitive Operator">*</a> <a id="6775" href="simple_essence.html#6763" class="Bound">y</a><a id="6776" class="Symbol">)}</a>
    <a id="6783" class="Symbol">}</a>

<a id="6786" class="Keyword">record</a> <a id="LinMap"></a><a id="6793" href="simple_essence.html#6793" class="Record">LinMap</a> <a id="6800" class="Symbol">(</a><a id="6801" href="simple_essence.html#6801" class="Bound">A</a> <a id="6803" class="Symbol">:</a> <a id="6805" class="PrimitiveType">Set</a> <a id="6809" href="simple_essence.html#5253" class="Bound">a</a><a id="6810" class="Symbol">)</a> <a id="6812" class="Symbol">(</a><a id="6813" href="simple_essence.html#6813" class="Bound">B</a> <a id="6815" class="Symbol">:</a> <a id="6817" class="PrimitiveType">Set</a> <a id="6821" href="simple_essence.html#5253" class="Bound">a</a><a id="6822" class="Symbol">)</a>
              <a id="6838" class="Symbol">{{</a><a id="6840" href="simple_essence.html#6840" class="Bound">_</a> <a id="6842" class="Symbol">:</a> <a id="6844" href="simple_essence.html#5907" class="Record">Additive</a> <a id="6853" href="simple_essence.html#6801" class="Bound">A</a><a id="6854" class="Symbol">}}</a> <a id="6857" class="Symbol">{{</a><a id="6859" href="simple_essence.html#6859" class="Bound">_</a> <a id="6861" class="Symbol">:</a> <a id="6863" href="simple_essence.html#5907" class="Record">Additive</a> <a id="6872" href="simple_essence.html#6813" class="Bound">B</a><a id="6873" class="Symbol">}}</a>
              <a id="6890" class="Symbol">{{</a><a id="6892" href="simple_essence.html#6892" class="Bound">_</a> <a id="6894" class="Symbol">:</a> <a id="6896" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="6905" href="simple_essence.html#6801" class="Bound">A</a><a id="6906" class="Symbol">}}</a> <a id="6909" class="Symbol">{{</a><a id="6911" href="simple_essence.html#6911" class="Bound">_</a> <a id="6913" class="Symbol">:</a> <a id="6915" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="6924" href="simple_essence.html#6813" class="Bound">B</a><a id="6925" class="Symbol">}}</a>
              <a id="6942" class="Symbol">:</a> <a id="6944" class="PrimitiveType">Set</a> <a id="6948" href="simple_essence.html#5837" class="Function">ℓ</a> <a id="6950" class="Keyword">where</a>
  <a id="6958" class="Keyword">constructor</a> <a id="mkLM"></a><a id="6970" href="simple_essence.html#6970" class="InductiveConstructor">mkLM</a>
  <a id="6977" class="Keyword">field</a>
    <a id="LinMap.f"></a><a id="6987" href="simple_essence.html#6987" class="Field">f</a>      <a id="6994" class="Symbol">:</a> <a id="6996" href="simple_essence.html#6801" class="Bound">A</a> <a id="6998" class="Symbol">→</a> <a id="7000" href="simple_essence.html#6813" class="Bound">B</a>
    
    <a id="LinMap.adds"></a><a id="7011" href="simple_essence.html#7011" class="Field">adds</a>   <a id="7018" class="Symbol">:</a> <a id="7020" class="Symbol">∀</a> <a id="7022" class="Symbol">{</a><a id="7023" href="simple_essence.html#7023" class="Bound">a</a> <a id="7025" href="simple_essence.html#7025" class="Bound">b</a> <a id="7027" class="Symbol">:</a> <a id="7029" href="simple_essence.html#6801" class="Bound">A</a><a id="7030" class="Symbol">}</a>
             <a id="7045" class="Comment">---------------------</a>
           <a id="7078" class="Symbol">→</a> <a id="7080" href="simple_essence.html#6987" class="Field">f</a> <a id="7082" class="Symbol">(</a><a id="7083" href="simple_essence.html#7023" class="Bound">a</a> <a id="7085" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="7087" href="simple_essence.html#7025" class="Bound">b</a><a id="7088" class="Symbol">)</a> <a id="7090" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7092" href="simple_essence.html#6987" class="Field">f</a> <a id="7094" href="simple_essence.html#7023" class="Bound">a</a> <a id="7096" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="7098" href="simple_essence.html#6987" class="Field">f</a> <a id="7100" href="simple_essence.html#7025" class="Bound">b</a>

    <a id="LinMap.scales"></a><a id="7107" href="simple_essence.html#7107" class="Field">scales</a> <a id="7114" class="Symbol">:</a> <a id="7116" class="Symbol">∀</a> <a id="7118" class="Symbol">{</a><a id="7119" href="simple_essence.html#7119" class="Bound">s</a> <a id="7121" class="Symbol">:</a> <a id="7123" href="simple_essence.html#5867" class="Datatype">§</a><a id="7124" class="Symbol">}</a> <a id="7126" class="Symbol">{</a><a id="7127" href="simple_essence.html#7127" class="Bound">a</a> <a id="7129" class="Symbol">:</a> <a id="7131" href="simple_essence.html#6801" class="Bound">A</a><a id="7132" class="Symbol">}</a>
             <a id="7147" class="Comment">-------------------</a>
           <a id="7178" class="Symbol">→</a> <a id="7180" href="simple_essence.html#6987" class="Field">f</a> <a id="7182" class="Symbol">(</a><a id="7183" href="simple_essence.html#7119" class="Bound">s</a> <a id="7185" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="7187" href="simple_essence.html#7127" class="Bound">a</a><a id="7188" class="Symbol">)</a> <a id="7190" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7192" href="simple_essence.html#7119" class="Bound">s</a> <a id="7194" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="7196" href="simple_essence.html#6987" class="Field">f</a> <a id="7198" href="simple_essence.html#7127" class="Bound">a</a>
<a id="7200" class="Keyword">open</a> <a id="7205" href="simple_essence.html#6793" class="Module">LinMap</a> <a id="7212" class="Symbol">{{</a> <a id="7215" class="Symbol">...</a> <a id="7219" class="Symbol">}}</a>

<a id="7223" class="Comment">-- As per Conal&#39;s advice:</a>
<a id="7249" class="Comment">-- ⊸≈ = isEquivalence LinMap.f Eq.isEquivalence</a>
<a id="7297" class="Keyword">postulate</a>
  <a id="⊸≡"></a><a id="7309" href="simple_essence.html#7309" class="Postulate">⊸≡</a> <a id="7312" class="Symbol">:</a> <a id="7314" class="Symbol">{</a><a id="7315" href="simple_essence.html#7315" class="Bound">A</a> <a id="7317" href="simple_essence.html#7317" class="Bound">B</a> <a id="7319" class="Symbol">:</a> <a id="7321" class="PrimitiveType">Set</a> <a id="7325" href="simple_essence.html#5253" class="Bound">a</a><a id="7326" class="Symbol">}</a>
       <a id="7335" class="Symbol">{{</a><a id="7337" href="simple_essence.html#7337" class="Bound">_</a> <a id="7339" class="Symbol">:</a> <a id="7341" href="simple_essence.html#5907" class="Record">Additive</a> <a id="7350" href="simple_essence.html#7315" class="Bound">A</a><a id="7351" class="Symbol">}}</a> <a id="7354" class="Symbol">{{</a><a id="7356" href="simple_essence.html#7356" class="Bound">_</a> <a id="7358" class="Symbol">:</a> <a id="7360" href="simple_essence.html#5907" class="Record">Additive</a> <a id="7369" href="simple_essence.html#7317" class="Bound">B</a><a id="7370" class="Symbol">}}</a>
       <a id="7380" class="Symbol">{{</a><a id="7382" href="simple_essence.html#7382" class="Bound">_</a> <a id="7384" class="Symbol">:</a> <a id="7386" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="7395" href="simple_essence.html#7315" class="Bound">A</a><a id="7396" class="Symbol">}}</a> <a id="7399" class="Symbol">{{</a><a id="7401" href="simple_essence.html#7401" class="Bound">_</a> <a id="7403" class="Symbol">:</a> <a id="7405" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="7414" href="simple_essence.html#7317" class="Bound">B</a><a id="7415" class="Symbol">}}</a>
       <a id="7425" class="Symbol">{</a><a id="7426" href="simple_essence.html#7426" class="Bound">lm₁</a> <a id="7430" href="simple_essence.html#7430" class="Bound">lm₂</a> <a id="7434" class="Symbol">:</a> <a id="7436" href="simple_essence.html#6793" class="Record">LinMap</a> <a id="7443" href="simple_essence.html#7315" class="Bound">A</a> <a id="7445" href="simple_essence.html#7317" class="Bound">B</a><a id="7446" class="Symbol">}</a>
     <a id="7453" class="Symbol">→</a> <a id="7455" href="simple_essence.html#6987" class="Field">LinMap.f</a> <a id="7464" href="simple_essence.html#7426" class="Bound">lm₁</a> <a id="7468" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7470" href="simple_essence.html#6987" class="Field">LinMap.f</a> <a id="7479" href="simple_essence.html#7430" class="Bound">lm₂</a>
       <a id="7490" class="Comment">---------------------------</a>
     <a id="7523" class="Symbol">→</a> <a id="7525" href="simple_essence.html#7426" class="Bound">lm₁</a> <a id="7529" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7531" href="simple_essence.html#7430" class="Bound">lm₂</a>

<a id="7536" class="Keyword">record</a> <a id="VectorSpace"></a><a id="7543" href="simple_essence.html#7543" class="Record">VectorSpace</a> <a id="7555" class="Symbol">(</a><a id="7556" href="simple_essence.html#7556" class="Bound">A</a> <a id="7558" class="Symbol">:</a> <a id="7560" class="PrimitiveType">Set</a> <a id="7564" href="simple_essence.html#5253" class="Bound">a</a><a id="7565" class="Symbol">)</a>
                   <a id="7586" class="Symbol">{{</a><a id="7588" href="simple_essence.html#7588" class="Bound">_</a> <a id="7590" class="Symbol">:</a> <a id="7592" href="simple_essence.html#5907" class="Record">Additive</a> <a id="7601" href="simple_essence.html#7556" class="Bound">A</a><a id="7602" class="Symbol">}}</a> <a id="7605" class="Symbol">{{</a><a id="7607" href="simple_essence.html#7607" class="Bound">_</a> <a id="7609" class="Symbol">:</a> <a id="7611" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="7620" href="simple_essence.html#7556" class="Bound">A</a><a id="7621" class="Symbol">}}</a>
                   <a id="7643" class="Symbol">:</a> <a id="7645" class="PrimitiveType">Set</a> <a id="7649" href="simple_essence.html#5837" class="Function">ℓ</a> <a id="7651" class="Keyword">where</a>
  <a id="7659" class="Keyword">field</a>
    <a id="7669" class="Comment">-- As noted above, seems like I should have to define some properties relating these two.</a>
    <a id="VectorSpace.basisSet"></a><a id="7763" href="simple_essence.html#7763" class="Field">basisSet</a>    <a id="7775" class="Symbol">:</a> <a id="7777" href="Agda.Builtin.List.html#148" class="Datatype">List</a> <a id="7782" href="simple_essence.html#7556" class="Bound">A</a>
    <a id="VectorSpace._·_"></a><a id="7788" href="simple_essence.html#7788" class="Field Operator">_·_</a>         <a id="7800" class="Symbol">:</a> <a id="7802" href="simple_essence.html#7556" class="Bound">A</a> <a id="7804" class="Symbol">→</a> <a id="7806" href="simple_essence.html#7556" class="Bound">A</a> <a id="7808" class="Symbol">→</a> <a id="7810" href="simple_essence.html#5867" class="Datatype">§</a>
    <a id="7816" class="Comment">-- Added while solving the isomorphism below.</a>
    <a id="VectorSpace.·-distrib-⊕"></a><a id="7866" href="simple_essence.html#7866" class="Field">·-distrib-⊕</a> <a id="7878" class="Symbol">:</a> <a id="7880" class="Symbol">∀</a> <a id="7882" class="Symbol">{</a><a id="7883" href="simple_essence.html#7883" class="Bound">a</a> <a id="7885" href="simple_essence.html#7885" class="Bound">b</a> <a id="7887" href="simple_essence.html#7887" class="Bound">c</a> <a id="7889" class="Symbol">:</a> <a id="7891" href="simple_essence.html#7556" class="Bound">A</a><a id="7892" class="Symbol">}</a>
                  <a id="7912" class="Comment">-------------------------------</a>
                <a id="7960" class="Symbol">→</a> <a id="7962" href="simple_essence.html#7883" class="Bound">a</a> <a id="7964" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="7966" class="Symbol">(</a><a id="7967" href="simple_essence.html#7885" class="Bound">b</a> <a id="7969" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="7971" href="simple_essence.html#7887" class="Bound">c</a><a id="7972" class="Symbol">)</a> <a id="7974" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="7976" class="Symbol">(</a><a id="7977" href="simple_essence.html#7883" class="Bound">a</a> <a id="7979" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="7981" href="simple_essence.html#7885" class="Bound">b</a><a id="7982" class="Symbol">)</a> <a id="7984" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="7986" class="Symbol">(</a><a id="7987" href="simple_essence.html#7883" class="Bound">a</a> <a id="7989" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="7991" href="simple_essence.html#7887" class="Bound">c</a><a id="7992" class="Symbol">)</a>
    <a id="VectorSpace.·-comm-⊛"></a><a id="7998" href="simple_essence.html#7998" class="Field">·-comm-⊛</a>    <a id="8010" class="Symbol">:</a> <a id="8012" class="Symbol">∀</a> <a id="8014" class="Symbol">{</a><a id="8015" href="simple_essence.html#8015" class="Bound">s</a> <a id="8017" class="Symbol">:</a> <a id="8019" href="simple_essence.html#5867" class="Datatype">§</a><a id="8020" class="Symbol">}</a> <a id="8022" class="Symbol">{</a><a id="8023" href="simple_essence.html#8023" class="Bound">a</a> <a id="8025" href="simple_essence.html#8025" class="Bound">b</a> <a id="8027" class="Symbol">:</a> <a id="8029" href="simple_essence.html#7556" class="Bound">A</a><a id="8030" class="Symbol">}</a>
                  <a id="8050" class="Comment">-------------------------</a>
                <a id="8092" class="Symbol">→</a> <a id="8094" href="simple_essence.html#8023" class="Bound">a</a> <a id="8096" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="8098" class="Symbol">(</a><a id="8099" href="simple_essence.html#8015" class="Bound">s</a> <a id="8101" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="8103" href="simple_essence.html#8025" class="Bound">b</a><a id="8104" class="Symbol">)</a> <a id="8106" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8108" href="simple_essence.html#8015" class="Bound">s</a> <a id="8110" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="8112" class="Symbol">(</a><a id="8113" href="simple_essence.html#8023" class="Bound">a</a> <a id="8115" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="8117" href="simple_essence.html#8025" class="Bound">b</a><a id="8118" class="Symbol">)</a>
    <a id="8124" class="Comment">-- Aha! Here&#39;s that property relating `basisSet` and `(_·_)` I was hunching on.</a>
    <a id="8208" class="Comment">-- Needed to complete the definition of `mk↔`, below.</a>
    <a id="VectorSpace.orthonormal"></a><a id="8266" href="simple_essence.html#8266" class="Field">orthonormal</a> <a id="8278" class="Symbol">:</a> <a id="8280" class="Symbol">∀</a> <a id="8282" class="Symbol">{</a><a id="8283" href="simple_essence.html#8283" class="Bound">f</a> <a id="8285" class="Symbol">:</a> <a id="8287" href="simple_essence.html#7556" class="Bound">A</a> <a id="8289" class="Symbol">→</a> <a id="8291" href="simple_essence.html#5867" class="Datatype">§</a><a id="8292" class="Symbol">}</a>
                <a id="8310" class="Symbol">→</a> <a id="8312" class="Symbol">{</a><a id="8313" href="simple_essence.html#8313" class="Bound">x</a> <a id="8315" class="Symbol">:</a> <a id="8317" href="simple_essence.html#7556" class="Bound">A</a><a id="8318" class="Symbol">}</a>
                  <a id="8338" class="Comment">----------------------------------------------------------</a>
                <a id="8413" class="Symbol">→</a> <a id="8415" class="Symbol">(</a><a id="8416" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8422" class="Symbol">(λ</a> <a id="8425" href="simple_essence.html#8425" class="Bound">acc</a> <a id="8429" href="simple_essence.html#8429" class="Bound">v</a> <a id="8431" class="Symbol">→</a> <a id="8433" href="simple_essence.html#8425" class="Bound">acc</a> <a id="8437" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="8439" class="Symbol">(</a><a id="8440" href="simple_essence.html#8283" class="Bound">f</a> <a id="8442" href="simple_essence.html#8429" class="Bound">v</a><a id="8443" class="Symbol">)</a> <a id="8445" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="8447" href="simple_essence.html#8429" class="Bound">v</a><a id="8448" class="Symbol">)</a> <a id="8450" href="simple_essence.html#6020" class="Field">id⊕</a> <a id="8454" href="simple_essence.html#7763" class="Field">basisSet</a><a id="8462" class="Symbol">)</a> <a id="8464" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="8466" href="simple_essence.html#8313" class="Bound">x</a> <a id="8468" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="8470" href="simple_essence.html#8283" class="Bound">f</a> <a id="8472" href="simple_essence.html#8313" class="Bound">x</a>
<a id="8474" class="Keyword">open</a> <a id="8479" href="simple_essence.html#7543" class="Module">VectorSpace</a> <a id="8491" class="Symbol">{{</a> <a id="8494" class="Symbol">...</a> <a id="8498" class="Symbol">}}</a>

<a id="8502" class="Comment">-- The Isomorphism I&#39;m trying to prove.</a>
<a id="a⊸§→a"></a><a id="8542" href="simple_essence.html#8542" class="Function">a⊸§→a</a> <a id="8548" class="Symbol">:</a> <a id="8550" class="Symbol">{</a><a id="8551" href="simple_essence.html#8551" class="Bound">A</a> <a id="8553" class="Symbol">:</a> <a id="8555" class="PrimitiveType">Set</a> <a id="8559" href="simple_essence.html#5253" class="Bound">a</a><a id="8560" class="Symbol">}</a>
        <a id="8570" class="Symbol">{{</a><a id="8572" href="simple_essence.html#8572" class="Bound">_</a> <a id="8574" class="Symbol">:</a> <a id="8576" href="simple_essence.html#5907" class="Record">Additive</a> <a id="8585" href="simple_essence.html#8551" class="Bound">A</a><a id="8586" class="Symbol">}}</a> <a id="8589" class="Symbol">{{</a><a id="8591" href="simple_essence.html#8591" class="Bound">_</a> <a id="8593" class="Symbol">:</a> <a id="8595" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="8604" href="simple_essence.html#8551" class="Bound">A</a><a id="8605" class="Symbol">}}</a>
        <a id="8616" class="Symbol">{{</a><a id="8618" href="simple_essence.html#8618" class="Bound">_</a> <a id="8620" class="Symbol">:</a> <a id="8622" href="simple_essence.html#7543" class="Record">VectorSpace</a> <a id="8634" href="simple_essence.html#8551" class="Bound">A</a><a id="8635" class="Symbol">}}</a>
        <a id="8646" class="Comment">-------------------------------------</a>
      <a id="8690" class="Symbol">→</a> <a id="8692" href="simple_essence.html#6793" class="Record">LinMap</a> <a id="8699" href="simple_essence.html#8551" class="Bound">A</a> <a id="8701" href="simple_essence.html#5867" class="Datatype">§</a> <a id="8703" class="Symbol">→</a> <a id="8705" href="simple_essence.html#8551" class="Bound">A</a>
<a id="8707" href="simple_essence.html#8542" class="Function">a⊸§→a</a> <a id="8713" class="Symbol">=</a> <a id="8715" class="Symbol">λ</a> <a id="8717" class="Symbol">{</a> <a id="8719" href="simple_essence.html#8719" class="Bound">lm</a> <a id="8722" class="Symbol">→</a> <a id="8724" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="8730" class="Symbol">(λ</a> <a id="8733" href="simple_essence.html#8733" class="Bound">acc</a> <a id="8737" href="simple_essence.html#8737" class="Bound">v</a> <a id="8739" class="Symbol">→</a> <a id="8741" href="simple_essence.html#8733" class="Bound">acc</a> <a id="8745" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="8747" class="Symbol">(</a><a id="8748" href="simple_essence.html#6987" class="Field">LinMap.f</a> <a id="8757" href="simple_essence.html#8719" class="Bound">lm</a> <a id="8760" href="simple_essence.html#8737" class="Bound">v</a><a id="8761" class="Symbol">)</a> <a id="8763" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="8765" href="simple_essence.html#8737" class="Bound">v</a><a id="8766" class="Symbol">)</a> <a id="8768" href="simple_essence.html#6020" class="Field">id⊕</a> <a id="8772" href="simple_essence.html#7763" class="Field">basisSet</a> <a id="8781" class="Symbol">}</a>

<a id="a⊸§←a"></a><a id="8784" href="simple_essence.html#8784" class="Function">a⊸§←a</a> <a id="8790" class="Symbol">:</a> <a id="8792" class="Symbol">{</a><a id="8793" href="simple_essence.html#8793" class="Bound">A</a> <a id="8795" class="Symbol">:</a> <a id="8797" class="PrimitiveType">Set</a> <a id="8801" href="simple_essence.html#5253" class="Bound">a</a><a id="8802" class="Symbol">}</a>
        <a id="8812" class="Symbol">{{</a><a id="8814" href="simple_essence.html#8814" class="Bound">_</a> <a id="8816" class="Symbol">:</a> <a id="8818" href="simple_essence.html#5907" class="Record">Additive</a> <a id="8827" href="simple_essence.html#8793" class="Bound">A</a><a id="8828" class="Symbol">}}</a> <a id="8831" class="Symbol">{{</a><a id="8833" href="simple_essence.html#8833" class="Bound">_</a> <a id="8835" class="Symbol">:</a> <a id="8837" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="8846" href="simple_essence.html#8793" class="Bound">A</a><a id="8847" class="Symbol">}}</a>
        <a id="8858" class="Symbol">{{</a><a id="8860" href="simple_essence.html#8860" class="Bound">_</a> <a id="8862" class="Symbol">:</a> <a id="8864" href="simple_essence.html#7543" class="Record">VectorSpace</a> <a id="8876" href="simple_essence.html#8793" class="Bound">A</a><a id="8877" class="Symbol">}}</a>
        <a id="8888" class="Comment">-------------------------------------</a>
      <a id="8932" class="Symbol">→</a> <a id="8934" href="simple_essence.html#8793" class="Bound">A</a> <a id="8936" class="Symbol">→</a> <a id="8938" href="simple_essence.html#6793" class="Record">LinMap</a> <a id="8945" href="simple_essence.html#8793" class="Bound">A</a> <a id="8947" href="simple_essence.html#5867" class="Datatype">§</a>
<a id="8949" href="simple_essence.html#8784" class="Function">a⊸§←a</a> <a id="8955" class="Symbol">=</a> <a id="8957" class="Symbol">λ</a> <a id="8959" class="Symbol">{</a> <a id="8961" href="simple_essence.html#8961" class="Bound">a</a> <a id="8963" class="Symbol">→</a> <a id="8965" href="simple_essence.html#6970" class="InductiveConstructor">mkLM</a> <a id="8970" class="Symbol">(</a><a id="8971" href="simple_essence.html#8961" class="Bound">a</a> <a id="8973" href="simple_essence.html#7788" class="Field Operator">·_</a><a id="8975" class="Symbol">)</a> <a id="8977" href="simple_essence.html#7866" class="Field">·-distrib-⊕</a> <a id="8989" href="simple_essence.html#7998" class="Field">·-comm-⊛</a> <a id="8998" class="Symbol">}</a>

<a id="9001" class="Comment">-- Danger, Will Robinson!</a>
<a id="9027" class="Keyword">postulate</a>
  <a id="x·z≡y·z→x≡y"></a><a id="9039" href="simple_essence.html#9039" class="Postulate">x·z≡y·z→x≡y</a> <a id="9051" class="Symbol">:</a> <a id="9053" class="Symbol">{</a><a id="9054" href="simple_essence.html#9054" class="Bound">A</a> <a id="9056" class="Symbol">:</a> <a id="9058" class="PrimitiveType">Set</a> <a id="9062" href="simple_essence.html#5253" class="Bound">a</a><a id="9063" class="Symbol">}</a>
                <a id="9081" class="Symbol">{{</a><a id="9083" href="simple_essence.html#9083" class="Bound">_</a> <a id="9085" class="Symbol">:</a> <a id="9087" href="simple_essence.html#5907" class="Record">Additive</a> <a id="9096" href="simple_essence.html#9054" class="Bound">A</a><a id="9097" class="Symbol">}}</a> <a id="9100" class="Symbol">{{</a><a id="9102" href="simple_essence.html#9102" class="Bound">_</a> <a id="9104" class="Symbol">:</a> <a id="9106" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="9115" href="simple_essence.html#9054" class="Bound">A</a><a id="9116" class="Symbol">}}</a> <a id="9119" class="Symbol">{{</a><a id="9121" href="simple_essence.html#9121" class="Bound">_</a> <a id="9123" class="Symbol">:</a> <a id="9125" href="simple_essence.html#7543" class="Record">VectorSpace</a> <a id="9137" href="simple_essence.html#9054" class="Bound">A</a><a id="9138" class="Symbol">}}</a>
                <a id="9157" class="Symbol">{</a><a id="9158" href="simple_essence.html#9158" class="Bound">x</a> <a id="9160" href="simple_essence.html#9160" class="Bound">y</a> <a id="9162" class="Symbol">:</a> <a id="9164" href="simple_essence.html#9054" class="Bound">A</a><a id="9165" class="Symbol">}</a>
              <a id="9181" class="Symbol">→</a> <a id="9183" class="Symbol">(∀</a> <a id="9186" class="Symbol">{</a><a id="9187" href="simple_essence.html#9187" class="Bound">z</a> <a id="9189" class="Symbol">:</a> <a id="9191" href="simple_essence.html#9054" class="Bound">A</a><a id="9192" class="Symbol">}</a> <a id="9194" class="Symbol">→</a> <a id="9196" href="simple_essence.html#9158" class="Bound">x</a> <a id="9198" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="9200" href="simple_essence.html#9187" class="Bound">z</a> <a id="9202" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9204" href="simple_essence.html#9160" class="Bound">y</a> <a id="9206" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="9208" href="simple_essence.html#9187" class="Bound">z</a><a id="9209" class="Symbol">)</a>
                <a id="9227" class="Comment">-----------------------------------------------------------</a>
              <a id="9301" class="Symbol">→</a> <a id="9303" href="simple_essence.html#9158" class="Bound">x</a> <a id="9305" href="Agda.Builtin.Equality.html#151" class="Datatype Operator">≡</a> <a id="9307" href="simple_essence.html#9160" class="Bound">y</a>
<a id="9309" class="Comment">-- ToDo: Try replacing postulate above w/ definition below.</a>
<a id="9369" class="Comment">--       (Perhaps, a proof by contradiction, starting w/ `x ≢ y`?)</a>
<a id="9436" class="Comment">-- x·z≡y·z→x≡y x·z≡y·z = {!!}</a>

<a id="a⊸§↔a"></a><a id="9467" href="simple_essence.html#9467" class="Function">a⊸§↔a</a> <a id="9473" class="Symbol">:</a> <a id="9475" class="Symbol">{</a><a id="9476" href="simple_essence.html#9476" class="Bound">A</a> <a id="9478" class="Symbol">:</a> <a id="9480" class="PrimitiveType">Set</a> <a id="9484" href="simple_essence.html#5253" class="Bound">a</a><a id="9485" class="Symbol">}</a>
        <a id="9495" class="Symbol">{{</a><a id="9497" href="simple_essence.html#9497" class="Bound">_</a> <a id="9499" class="Symbol">:</a> <a id="9501" href="simple_essence.html#5907" class="Record">Additive</a> <a id="9510" href="simple_essence.html#9476" class="Bound">A</a><a id="9511" class="Symbol">}}</a> <a id="9514" class="Symbol">{{</a><a id="9516" href="simple_essence.html#9516" class="Bound">_</a> <a id="9518" class="Symbol">:</a> <a id="9520" href="simple_essence.html#6521" class="Record">Scalable</a> <a id="9529" href="simple_essence.html#9476" class="Bound">A</a><a id="9530" class="Symbol">}}</a>
        <a id="9541" class="Symbol">{{</a><a id="9543" href="simple_essence.html#9543" class="Bound">_</a> <a id="9545" class="Symbol">:</a> <a id="9547" href="simple_essence.html#7543" class="Record">VectorSpace</a> <a id="9559" href="simple_essence.html#9476" class="Bound">A</a><a id="9560" class="Symbol">}}</a>
        <a id="9571" class="Comment">-------------------------------------</a>
      <a id="9615" class="Symbol">→</a> <a id="9617" class="Symbol">(</a><a id="9618" href="simple_essence.html#6793" class="Record">LinMap</a> <a id="9625" href="simple_essence.html#9476" class="Bound">A</a> <a id="9627" href="simple_essence.html#5867" class="Datatype">§</a><a id="9628" class="Symbol">)</a> <a id="9630" href="Function.Bundles.html#7902" class="Function Operator">↔</a> <a id="9632" href="simple_essence.html#9476" class="Bound">A</a>
<a id="9634" href="simple_essence.html#9467" class="Function">a⊸§↔a</a> <a id="9640" class="Symbol">{</a><a id="9641" href="simple_essence.html#9641" class="Bound">A</a><a id="9642" class="Symbol">}</a> <a id="9644" class="Symbol">=</a>
  <a id="9648" href="Function.Bundles.html#9488" class="Function">mk↔</a> <a id="9652" class="Symbol">{</a><a id="9653" class="Argument">f</a> <a id="9655" class="Symbol">=</a> <a id="9657" href="simple_essence.html#8542" class="Function">a⊸§→a</a><a id="9662" class="Symbol">}</a> <a id="9664" class="Symbol">{</a><a id="9665" class="Argument">f⁻¹</a> <a id="9669" class="Symbol">=</a> <a id="9671" href="simple_essence.html#8784" class="Function">a⊸§←a</a><a id="9676" class="Symbol">}</a>
      <a id="9684" class="Symbol">(</a> <a id="9686" class="Symbol">(λ</a> <a id="9689" class="Symbol">{</a><a id="9690" href="simple_essence.html#9690" class="Bound">x</a> <a id="9692" class="Symbol">→</a> <a id="9694" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="9718" href="simple_essence.html#8542" class="Function">a⊸§→a</a> <a id="9724" class="Symbol">(</a><a id="9725" href="simple_essence.html#8784" class="Function">a⊸§←a</a> <a id="9731" href="simple_essence.html#9690" class="Bound">x</a><a id="9732" class="Symbol">)</a>
                <a id="9750" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9772" href="simple_essence.html#8542" class="Function">a⊸§→a</a> <a id="9778" class="Symbol">(</a><a id="9779" href="simple_essence.html#6970" class="InductiveConstructor">mkLM</a> <a id="9784" class="Symbol">(</a><a id="9785" href="simple_essence.html#9690" class="Bound">x</a> <a id="9787" href="simple_essence.html#7788" class="Field Operator">·_</a><a id="9789" class="Symbol">)</a> <a id="9791" href="simple_essence.html#7866" class="Field">·-distrib-⊕</a> <a id="9803" href="simple_essence.html#7998" class="Field">·-comm-⊛</a><a id="9811" class="Symbol">)</a>
                <a id="9829" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="9851" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="9857" class="Symbol">(λ</a> <a id="9860" href="simple_essence.html#9860" class="Bound">acc</a> <a id="9864" href="simple_essence.html#9864" class="Bound">v</a> <a id="9866" class="Symbol">→</a> <a id="9868" href="simple_essence.html#9860" class="Bound">acc</a> <a id="9872" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="9874" class="Symbol">(</a><a id="9875" href="simple_essence.html#9690" class="Bound">x</a> <a id="9877" href="simple_essence.html#7788" class="Field Operator">·</a> <a id="9879" href="simple_essence.html#9864" class="Bound">v</a><a id="9880" class="Symbol">)</a> <a id="9882" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="9884" href="simple_essence.html#9864" class="Bound">v</a><a id="9885" class="Symbol">)</a> <a id="9887" href="simple_essence.html#6020" class="Field">id⊕</a> <a id="9891" href="simple_essence.html#7763" class="Field">basisSet</a>
                <a id="9916" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="9919" href="simple_essence.html#9039" class="Postulate">x·z≡y·z→x≡y</a> <a id="9931" class="Symbol">(</a><a id="9932" href="simple_essence.html#8266" class="Field">orthonormal</a> <a id="9944" class="Symbol">{</a><a id="9945" class="Argument">f</a> <a id="9947" class="Symbol">=</a> <a id="9949" class="Symbol">(</a><a id="9950" href="simple_essence.html#9690" class="Bound">x</a> <a id="9952" href="simple_essence.html#7788" class="Field Operator">·_</a><a id="9954" class="Symbol">)})</a> <a id="9958" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="9978" href="simple_essence.html#9690" class="Bound">x</a>
                <a id="9996" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="9997" class="Symbol">})</a>
      <a id="10006" href="Agda.Builtin.Sigma.html#236" class="InductiveConstructor Operator">,</a> <a id="10008" class="Symbol">λ</a> <a id="10010" class="Symbol">{</a><a id="10011" href="simple_essence.html#10011" class="Bound">lm</a> <a id="10014" class="Symbol">→</a> <a id="10016" href="Relation.Binary.PropositionalEquality.Core.html#2517" class="Function Operator">begin</a>
                  <a id="10040" href="simple_essence.html#8784" class="Function">a⊸§←a</a> <a id="10046" class="Symbol">(</a><a id="10047" href="simple_essence.html#8542" class="Function">a⊸§→a</a> <a id="10053" href="simple_essence.html#10011" class="Bound">lm</a><a id="10055" class="Symbol">)</a>
                <a id="10073" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10095" href="simple_essence.html#8784" class="Function">a⊸§←a</a> <a id="10101" class="Symbol">(</a><a id="10102" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10108" class="Symbol">(λ</a> <a id="10111" href="simple_essence.html#10111" class="Bound">acc</a> <a id="10115" href="simple_essence.html#10115" class="Bound">v</a> <a id="10117" class="Symbol">→</a> <a id="10119" href="simple_essence.html#10111" class="Bound">acc</a> <a id="10123" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="10125" class="Symbol">(</a><a id="10126" href="simple_essence.html#6987" class="Field">LinMap.f</a> <a id="10135" href="simple_essence.html#10011" class="Bound">lm</a> <a id="10138" href="simple_essence.html#10115" class="Bound">v</a><a id="10139" class="Symbol">)</a> <a id="10141" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="10143" href="simple_essence.html#10115" class="Bound">v</a><a id="10144" class="Symbol">)</a> <a id="10146" href="simple_essence.html#6020" class="Field">id⊕</a> <a id="10150" href="simple_essence.html#7763" class="Field">basisSet</a><a id="10158" class="Symbol">)</a>
                <a id="10176" href="Relation.Binary.PropositionalEquality.Core.html#2575" class="Function Operator">≡⟨⟩</a>
                  <a id="10198" href="simple_essence.html#6970" class="InductiveConstructor">mkLM</a> <a id="10203" class="Symbol">((</a><a id="10205" href="Data.List.Base.html#3726" class="Function">foldl</a> <a id="10211" class="Symbol">(λ</a> <a id="10214" href="simple_essence.html#10214" class="Bound">acc</a> <a id="10218" href="simple_essence.html#10218" class="Bound">v</a> <a id="10220" class="Symbol">→</a> <a id="10222" href="simple_essence.html#10214" class="Bound">acc</a> <a id="10226" href="simple_essence.html#6033" class="Field Operator">⊕</a> <a id="10228" class="Symbol">(</a><a id="10229" href="simple_essence.html#6987" class="Field">LinMap.f</a> <a id="10238" href="simple_essence.html#10011" class="Bound">lm</a> <a id="10241" href="simple_essence.html#10218" class="Bound">v</a><a id="10242" class="Symbol">)</a> <a id="10244" href="simple_essence.html#6634" class="Field Operator">⊛</a> <a id="10246" href="simple_essence.html#10218" class="Bound">v</a><a id="10247" class="Symbol">)</a> <a id="10249" href="simple_essence.html#6020" class="Field">id⊕</a> <a id="10253" href="simple_essence.html#7763" class="Field">basisSet</a><a id="10261" class="Symbol">)</a><a id="10262" href="simple_essence.html#7788" class="Field Operator">·_</a><a id="10264" class="Symbol">)</a>
                       <a id="10289" href="simple_essence.html#7866" class="Field">·-distrib-⊕</a> <a id="10301" href="simple_essence.html#7998" class="Field">·-comm-⊛</a>
                <a id="10326" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">≡⟨</a> <a id="10329" href="simple_essence.html#7309" class="Postulate">⊸≡</a> <a id="10332" class="Symbol">(</a> <a id="10334" href="simple_essence.html#5786" class="Postulate">extensionality</a>
                          <a id="10375" class="Symbol">(</a> <a id="10377" class="Symbol">λ</a> <a id="10379" href="simple_essence.html#10379" class="Bound">x</a> <a id="10381" class="Symbol">→</a> <a id="10383" href="simple_essence.html#8266" class="Field">orthonormal</a> <a id="10395" class="Symbol">{</a><a id="10396" class="Argument">f</a> <a id="10398" class="Symbol">=</a> <a id="10400" href="simple_essence.html#6987" class="Field">LinMap.f</a> <a id="10409" href="simple_essence.html#10011" class="Bound">lm</a><a id="10411" class="Symbol">}</a> <a id="10413" class="Symbol">{</a><a id="10414" class="Argument">x</a> <a id="10416" class="Symbol">=</a> <a id="10418" href="simple_essence.html#10379" class="Bound">x</a><a id="10419" class="Symbol">}</a> <a id="10421" class="Symbol">)</a>
                      <a id="10445" class="Symbol">)</a>
                 <a id="10464" href="Relation.Binary.PropositionalEquality.Core.html#2634" class="Function">⟩</a>
                  <a id="10484" href="simple_essence.html#10011" class="Bound">lm</a>
                <a id="10503" href="Relation.Binary.PropositionalEquality.Core.html#2816" class="Function Operator">∎</a><a id="10504" class="Symbol">}</a>
      <a id="10512" class="Symbol">)</a>

<a id="10515" class="Comment">-- This, done in response to Conal&#39;s suggestion of using `Equivalence`, instead of</a>
<a id="10598" class="Comment">-- `Equality`, compiles fine but seems too easy and too weak.</a>
<a id="10660" class="Comment">-- There&#39;s no guarantee of returning back where we started after a double pass, for instance.</a>
<a id="10754" class="Comment">-- I think that I didn&#39;t fully grok the hint he was giving me.</a>
<a id="10817" class="Comment">--</a>
<a id="10820" class="Comment">-- a⊸§⇔a : {A : Set a}</a>
<a id="10843" class="Comment">--         {{_ : Additive A}} {{_ : Scalable A}}</a>
<a id="10892" class="Comment">--         {{_ : VectorSpace A}}</a>
<a id="10925" class="Comment">--         -------------------------------------</a>
<a id="10974" class="Comment">--       → (LinMap A §) ⇔ A</a>
<a id="11002" class="Comment">-- a⊸§⇔a {A} = mk⇔ a⊸§→a a⊸§←a</a>

</pre>
