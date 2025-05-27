---
author:  P. Martin-Löf
hauthor: Per Martin-Löf
year:    2006
title:   '100 years of Zermelo’s axiom of choice: What was the problem with it?'
htitle:  '100 years of Zermelo’s<br>axiom of choice:<br>What was the problem with it?'
lang:    en
wip:     yes
card:
  - P. Martin-Löf (2006)
  - '[100 years of Zermelo’s axiom of choice: What was the problem with it?
    ](https://sci-hub.st/10.1093/comjnl/bxh162)'
  - '*Comp. J.*, Vol. 49(3), pp. 345–350.'
todo:
  - '(8) DOI not on sci-hub; https://doi.org/10.24033/bsmf.761'
  - (10) both DOIs missing
  - (11) DOI missing
  - (20) document missing
---


```
-- Partially mechanised by Miëtek Bak
-- TODO: Theorem 2

module mi.MartinLof2006 where

open import Agda.Primitive using (Level ; _⊔_ ; lsuc)

id : ∀ {𝓈} {S : Set 𝓈} → S → S
id x = x

infixr 9 _∘_
_∘_ : ∀ {𝓈 𝓉 𝓊} {S : Set 𝓈} {T : S → Set 𝓉} {U : ∀ {x} → T x → Set 𝓊}
        (f : ∀ {x} (y : T x) → U y) (g : ∀ x → T x) (x : S) → U (g x)
(f ∘ g) x = f (g x)

Relation : ∀ {𝓈} (S : Set 𝓈) ℓ → Set _
Relation S ℓ = S → S → Set ℓ

Reflexive : ∀ {𝓈 ℓ} {S : Set 𝓈} (_∼_ : Relation S ℓ) → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x

Symmetric : ∀ {𝓈 ℓ} {S : Set 𝓈} (_∼_ : Relation S ℓ) → Set _
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x

Transitive : ∀ {𝓈 ℓ} {S : Set 𝓈} (_∼_ : Relation S ℓ) → Set _
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

record Equivalence {𝓈} (S : Set 𝓈) ℯ : Set (𝓈 ⊔ lsuc ℯ) where
  field _≍_     : Relation S ℯ
        ≍-refl  : Reflexive _≍_
        ≍-sym   : Symmetric _≍_
        ≍-trans : Transitive _≍_

open Equivalence {{...}}

open import Agda.Builtin.Equality using (refl) renaming (_≡_ to Id)

sym : ∀ {𝓈} {S : Set 𝓈} → Symmetric {S = S} Id
sym refl = refl

trans : ∀ {𝓈} {S : Set 𝓈} → Transitive {S = S} Id
trans refl h = h

Id-≍ : ∀ {𝓈} {S : Set 𝓈} → Equivalence S _
Id-≍ = record { _≍_     = Id
              ; ≍-refl  = refl
              ; ≍-sym   = sym
              ; ≍-trans = trans
              }

cong : ∀ {𝓈 𝓉} {S : Set 𝓈} {T : Set 𝓉} (f : S → T) {x y : S} →
       Id x y → Id (f x) (f y)
cong f refl = refl

Id→≍ : ∀ {𝓈 ℯ} {S : Set 𝓈} {x y : S} {{≍S : Equivalence S ℯ}} →
        Id x y → x ≍ y
Id→≍ refl = ≍-refl

open import Agda.Builtin.Sigma using (_,_ ; fst ; snd) renaming (Σ to ∃)

infix 2 ∃-syntax
syntax ∃-syntax S (λ x → T) = ∃[ x ⦂ S ] T
∃-syntax : ∀ {𝓈 𝓉} (S : Set 𝓈) (T : S → Set 𝓉) → Set _
∃-syntax = ∃

infixr 2 _∧_
_∧_ : ∀ {𝓈 𝓉} (S : Set 𝓈) (T : Set 𝓉) → Set _
S ∧ T = ∃[ _ ⦂ S ] T

infix 2 ∃!-syntax
syntax ∃!-syntax S (λ x → T) = ∃![ x ⦂ S ] T
∃!-syntax : ∀ {𝓈 𝓉 ℯ} (S : Set 𝓈) (T : S → Set 𝓉) {{≍S : Equivalence S ℯ}} → Set _
∃!-syntax S T = ∃[ x ⦂ S ] T x ∧ ∀ {y} → T y → x ≍ y

infix 1 _↔_
_↔_ : ∀ {𝓈 𝓉} (S : Set 𝓈) (T : Set 𝓉) → Set _
S ↔ T = (S → T) ∧ (T → S)

↔-refl : ∀ {𝓈} → Reflexive {S = Set 𝓈} _↔_
↔-refl = id , id

↔-sym : ∀ {𝓈} → Symmetric {S = Set 𝓈} _↔_
↔-sym (f , f⁻¹) = f⁻¹ , f

↔-trans : ∀ {𝓈} → Transitive {S = Set 𝓈} _↔_
↔-trans (f , f⁻¹) (g , g⁻¹) = g ∘ f , f⁻¹ ∘ g⁻¹

↔-≍ : ∀ {𝓈} → Equivalence (Set 𝓈) _
↔-≍ = record { _≍_     = _↔_
              ; ≍-refl  = ↔-refl
              ; ≍-sym   = ↔-sym
              ; ≍-trans = ↔-trans
              }

Subset : ∀ {𝓈} (S : Set 𝓈) 𝒶 → Set _
Subset S 𝒶 = S → Set 𝒶

_∩_ : ∀ {𝓈 𝒶 𝒷} {S : Set 𝓈} (A : Subset S 𝒶) (B : Subset S 𝒷) → Subset S _
(A ∩ B) x = A x ∧ B x
```

Cantor conceived set theory in a sequence of six papers published in the *[Mathematische Annalen
]{lang=de}* during the five year period 1879–1884.  In the fifth of these papers, published in
1883,[^1] he stated as a law of thought (*[Denkgesetz]{lang=de}*) that every set can be well-ordered
or, more precisely, that it is always possible to bring any well-defined set into the form of a
well-ordered set.  Now to call it a law of thought was implicitly to claim self-evidence for it, but
he must have given up that claim at some point, because in the 1890s he made an unsuccessful
attempt at demonstrating the well-ordering principle.[^2]

The first to succeed in doing so was Zermelo,[^3] although, as a prerequisite of the demonstration,
he had to introduce a new principle, which came to be called the principle of choice (*[Prinzip der
Auswahl]{lang=de}*) respectively the axiom of choice (*[Axiom der Auswahl]{lang=de}*) in his two[^4]
papers[^5] from 1908.  His first paper on the subject, published in 1904, consists of merely three
pages, excerpted by Hilbert from a letter which he had received from Zermelo.  The letter is dated
24 September 1904, and the excerpt begins by saying that the demonstration came out of discussions
with Erhard Schmidt during the preceding week, which means that we can safely date the appearance of
the axiom of choice and the demonstration of the well-ordering theorem to September 1904.

Brief as it was, Zermelo’s paper gave rise to what is presumably the most lively discussion among
mathematicians on the validity, or acceptability, of a mathematical axiom that has ever taken place.
Within a couple of years, written contributions to this discussion were published by Felix
Bernstein, Schoenflies, Hamel, Hessenberg, and Hausdorff in Germany; Baire, Borel, Hadamard,
Lebesgue, Richard, and Poincaré in France; Hobson, Hardy, Jourdain, and Russell in England; Julius
König in Hungary; Peano in Italy, and Brouwer in the Netherlands.[^6]  Zermelo responded to those
of these contributions that were critical, which was a majority, in a second paper from 1908.  This
second paper also contains a new proof of the well-ordering theorem, less intuitive or less
perspicuous, it has to be admitted, than the original proof, as well as a new formulation of the
axiom of choice, a formulation which will play a crucial role in the following considerations.

Despite the strength of the initial opposition against it, Zermelo’s axiom of choice gradually came
to be accepted, mainly because it was needed at an early stage in the development of several
branches of mathematics, not only set theory, but also topology, algebra and functional analysis,
for example.  Towards the end of the thirties, it had become firmly established and was made part of
the standard mathematical curriculum in the form of Zorn’s lemma.[^7]

The intuitionists, on the other hand, rejected the axiom of choice from the very beginning.  Baire,
Borel, and Lebesgue were all critical of it in their contributions to the correspondence, which was
published under the title *[Cinq lettres sur la théorie des ensembles]{lang=fr}* in 1905.[^8]
Brouwer’s thesis from 1907 contains a section on the well-ordering principle in which it is treated
in a dismissive fashion (‘of course there is no motivation for this at all’) and in which, following
Borel,[^9] he belittles Zermelo’s proof of it from the axiom of choice.[^10]  No further discussion
of the axiom of choice seems to be found in either Brouwer’s or Heyting’s writings.  Presumably, it
was regarded by them as a prime example of a nonconstructive principle.

::: {.align}
It therefore came as a surprise when, as late as in 1967, Bishop stated,

> A choice function exists in constructive mathematics, because a choice is *implied by the very
> meaning of existence*,[^11]

although, in the terminology that he himself introduced in the subsequent chapter, he ought to have
said ‘choice operation’ rather than ‘choice function’.  What he had in mind was clearly that the
truth of

$$(∀i : I)(∃x : S)A(i, x) → (∃f : I → S)(∀i : I)A(i, f(i))$$

and even, more generally,

$$(∀i : I)(∃x : S_i)A(i, x) → (∃f : Π_{i : I} S_i)(∀i : I)A(i, f(i))$$

becomes evident almost immediately upon remembering the Brouwer-Heyting-Kolmogorov interpretation
of the logical constants, which means that it might as well have been observed already in the early
thirties.  And it is this intuitive justification that was turned into a formal proof in
constructive type theory, a proof that effectively uses the strong rule of $∃$-elimination that
became possible to formulate as a result of having made the proof objects appear in the system
itself and not only in its interpretation.

```
-- (intensional, constructive, type-theoretic) axiom of choice
AC : ∀ ℓ → Set _
AC ℓ = ∀ {I S : Set ℓ} {A : I → Subset S ℓ} →
         (∀ i → ∃[ x ⦂ S ] A i x) → ∃[ f ⦂ (I → S) ] ∀ i → A i (f i)

-- generalised axiom of choice
GAC : ∀ ℓ → Set _
GAC ℓ = ∀ {I : Set ℓ} {S : I → Set ℓ} {A : ∀ i → Subset (S i) ℓ} →
          (∀ i → ∃[ x ⦂ S i ] A i x) → ∃[ f ⦂ (∀ i → S i) ] ∀ i → A i (f i)

gac : ∀ {ℓ} → GAC ℓ
gac h = fst ∘ h , snd ∘ h

ac : ∀ {ℓ} → AC ℓ
ac = gac
```
:::

In 1975, soon after Bishop’s vindication of the constructive axiom of choice, Diaconescu proved
that, in topos theory, the law of excluded middle follows from the axiom of choice.[^12]  Now,
topos theory being an intuitionistic theory, albeit impredicative, this is on the surface of it
incompatible with Bishop’s observation because of the constructive unacceptability of the law of
excluded middle.  There is therefore a need to investigate how the constructive axiom of choice,
validated by the Brouwer-Heyting-Kolmogorov interpretation, is related to Zermelo’s axiom of choice
on the one hand and to the topos-theoretic axiom of choice on the other.

To this end, using constructive type theory as our instrument of analysis, let us simply try to
prove Zermelo’s axiom of choice.  This attempt should of course fail, but in the process of making
it we might at least be able to discover what it is that is really objectionable about it.  So what
was Zermelo’s axiom of choice?  In the original paper from 1904, he gave to it the following
formulation,

> [*Jeder Teilmenge $M'$ denke man sich ein beliebiges Element $m'_1$ zugeordnet, das in $M'$
> selbst vorkommt und das „ausgezeichnete” Element von $M'$ genannt werden möge.*]{lang=de}[^13]

Here $M'$ is an arbitrary subset, which contains at least one element, of a given set $M.$  What is
surprising about this formulation is that there is nothing objectionable about it from a
constructive point of view.  Indeed, the distinguished element $m'_1$ can be taken to be the first
projection of the proof of the existential proposition $(∃x : M)$$M'(x),$ which says that the
subset $M'$ of $M$ contains at least one element.  This means that one would have to go into the
demonstration of the well-ordering theorem in order to determine exactly what are its
nonconstructive ingredients.

Instead of doing that, I shall turn to the formulation of the axiom of choice that Zermelo favoured
in his second paper on the well-ordering theorem from 1908,

> [Axiom.  *Eine Menge $S,$ welche in eine Menge getrennter Teile $A,$ $B,$ $C,$ $…$ zerfällt,
> deren jeder mindestens ein Element enthält, besitzt mindestens eine Untermenge $S_1,$ welche mit
> jedem der betrachteten Teile $A,$ $B,$ $C,$ $…$ genau ein Element gemein hat.*]{lang=de}[^14]

::: {.align}
Formulated in this way, Zermelo’s axiom of choice turns out to coincide with the multiplicative
axiom, which Whitehead[^15] and Russell[^16] had found indispensable for the development of the
theory of cardinals.  The type-theoretic rendering of this formulation of the axiom of choice is
straightforward, once one remembers that a basic set in the sense of Cantorian set theory
corresponds to an exten&shy;sional set, that is, a set equipped with an equivalence relation, in
type theory, and that a subset of an exten&shy;sional set is interpreted as a propositional function
which is exten&shy;sional with respect to the equivalence relation in question.

```
Extensional : ∀ {𝓈 𝓉 ℯS ℯT} {S : Set 𝓈} {T : Set 𝓉} (f : S → T)
                {{≍S : Equivalence S ℯS}}{{≍T : Equivalence T ℯT}} → Set _
Extensional f = ∀ {x y} → x ≍ y → f x ≍ f y

Extensional-Id-≍ : ∀ {𝓈 𝓉 ℯT} {S : Set 𝓈} {T : Set 𝓉} (f : S → T)
                     {{≍T : Equivalence T ℯT}} → Set _
Extensional-Id-≍ f = Extensional f {{≍S = Id-≍}}

Extensional-≍-Id : ∀ {𝓈 𝓉 ℯS} {S : Set 𝓈} {T : Set 𝓉} (f : S → T)
                     {{≍S : Equivalence S ℯS}} → Set _
Extensional-≍-Id f = Extensional f {{≍T = Id-≍}}

Extensional-≍-↔ : ∀ {𝓈 𝒶 ℯS} {S : Set 𝓈} (f : Subset S 𝒶)
                     {{≍S : Equivalence S ℯS}} → Set _
Extensional-≍-↔ f = Extensional f {{≍T = ↔-≍}}
```
:::

::: {.align}
Thus the data of Zermelo’s 1908 formulation of the axiom of choice are a set $S,$ which comes
equipped with an equivalence relation $≍_S,$ and a family $(A_i)_{i : I}$ of propositional
functions on $S$ satisfying the following properties,

1.  $x ≍_S y → (A_i(x) ↔ A_i(y))$ (exten&shy;sionality),

2.  $i ≍_I j → (∀x : S)(A_i(x) ↔ A_j(x))$ (exten&shy;sionality of the dependence on the index),

3.  $(∃x : S)(A_i(x) ∧ A_j(x)) → i ≍_I j$ (mutual exclusive&shy;ness),

4.  $(∀x : S)(∃i : I)A_i(x)$ (exhaustiveness),

5.  $(∀i : I)(∃x : S)A_i(x)$ (nonemptiness).

Given these data, the axiom guarantees the existence of a propositional function $S_1$ on $S$ such
that

6.  $x ≍_S y → (S_1(x) ↔ S_1(y))$ (exten&shy;sionality),

7.  $(∀i : I)(∃!x : S)(A_i ∩ S_1)(x)$ (uniqueness of choice).

```
Extensional-≍S-↔ : ∀ {𝒾 𝓈 𝒶 ℯS} {I : Set 𝒾} {S : Set 𝓈} (A : I → Subset S 𝒶)
                      {{≍S : Equivalence S ℯS}} → Set _
Extensional-≍S-↔ A = ∀ {i} → Extensional-≍-↔ (A i)

Extensional-≍I-↔ : ∀ {𝒾 𝓈 𝒶 ℯI} {I : Set 𝒾} {S : Set 𝓈} (A : I → Subset S 𝒶)
                      {{≍I : Equivalence I ℯI}} → Set _
Extensional-≍I-↔ A = ∀ {x} → Extensional-≍-↔ (λ i → A i x)

MutuallyExclusive : ∀ {𝒾 𝓈 𝒶 ℯI} {I : Set 𝒾} {S : Set 𝓈} (A : I → Subset S 𝒶)
                      {{≍I : Equivalence I ℯI}} → Set _
MutuallyExclusive A = ∀ {i j x} → A i x → A j x → i ≍ j

Exhaustive : ∀ {𝒾 𝓈 𝒶} {I : Set 𝒾} {S : Set 𝓈} (A : I → Subset S 𝒶) → Set _
Exhaustive {I = I} A = ∀ x → ∃[ i ⦂ I ] A i x

Nonempty : ∀ {𝒾 𝓈 𝒶} {I : Set 𝒾} {S : Set 𝓈} (A : I → Subset S 𝒶) → Set _
Nonempty {S = S} A = ∀ i → ∃[ x ⦂ S ] A i x

-- Zermelo’s axiom of choice
ZAC : ∀ ℓ → Set _
ZAC ℓ = ∀ {I S : Set ℓ} {A : I → Subset S ℓ}
          {{≍I : Equivalence I ℓ}} {{≍S : Equivalence S ℓ}}
          (p₁ : Extensional-≍S-↔ A) (p₂ : Extensional-≍I-↔ A)
          (p₃ : MutuallyExclusive A) (p₄ : Exhaustive A)
          (p₅ : Nonempty A) →
        ∃[ S₁ ⦂ Subset S ℓ ] Extensional-≍-↔ S₁ ∧ ∀ i → ∃![ x ⦂ S ] (A i ∩ S₁) x
```
:::

::: {.align}
The obvious way of trying to prove (6) and (7) from (1)–(5) is to apply the type-theoretic
(constructive, inten&shy;sional) axiom of choice to (5), so as to get a function $f : I → S$ such
that

$$(∀i : I)A_i(f(i)),$$

and then define $S_1$ by the equation

$$S_1 = \{f(j)\ |\ j : I\} = \{x\ |\ (∃j : I)(f(j)) ≍_S x)\}.$$

Defined in this way, $S_1$ is clearly exten&shy;sional, which is to say that it satisfies (6).  What
about (7)?  Since the proposition

$$(A_i ∩ S_1)(f(i)) = A_i(f(i)) ∧ S_1(f(i))$$

is clearly true, so is

$$(∀i : I)(∃x : S)(A_i ∩ S_1)(x),$$

which means that only the uniqueness condition remains to be proved.  To this end, assume that the
proposition

$$(A_i ∩ S_1)(y) = A_i(y) ∧ S_1(y)$$

is true, that is, that the two propositions

$$
\begin{cases}
  A_i(y),\\
  S_1(y) = (∃j : I)(f(j) ≍_S y),
\end{cases}
$$

are both true.  Let $j : I$ satisfy $f(j) ≍_S y.$  Then, since $(∀i : I)$$A_i(f(i))$ is true, so is
$A_j(f(j)).$  Hence, by the exten&shy;sionality of $A_j$ with respect to $≍_S,$ $A_j(y)$ is true,
which, together with the assumed truth of $A_i(y),$ yields $i ≍_I j$ by the mutual exclusiveness of
the family of subsets $(A_i)_{i : I}.$  At this stage, in order to conclude that $f(i) ≍_S y,$ we
need to know that the choice function $f$ is exten&shy;sional, that is, that

$$i ≍_I j → f(i) ≍_S f(j).$$

This, however, is not guaranteed by the constructive, or inten&shy;sional, axiom of choice which
follows from the strong rule of $∃$-elimination in type theory.  Thus our attempt to prove Zermelo’s
axiom of choice has failed, as was to be expected.

On the other hand, we have succeeded in proving that Zermelo’s axiom of choice follows from the
exten&shy;sional axiom of choice

$$(∀i : I)(∃x : S)A_i(x) → (∃f : I → S)(\text{Ext}(f) ∧ (∀i : I)A_i(f(i))),$$

which I shall call ExtAC, where

$$\text{Ext}(f) ≍ (∀i, j: I)(i ≍_I j → f(i) ≍_S f(j)).$$

The only trouble with it is that it lacks the evidence of the inten&shy;sional axiom of choice,
which does not prevent one from investigating its consequences, of course.

```
-- extensional axiom of choice
EAC : ∀ ℓ → Set _
EAC ℓ = ∀ {I S : Set ℓ} {A : I → Subset S ℓ}
          {{≍I : Equivalence I ℓ}} {{≍S : Equivalence S ℓ}}
          (p₁ : Extensional-≍S-↔ A) (p₂ : Extensional-≍I-↔ A)
          (p₅ : Nonempty A) →
        ∃[ f ⦂ (I → S) ] Extensional f ∧ ∀ i → A i (f i)

eac→zac : ∀ {ℓ} → EAC ℓ → ZAC ℓ
eac→zac eac {I} {S} {A} p₁ p₂ p₃ p₄ p₅ = S₁ , p₆ , p₇
  where
    f : I → S
    f = fst (eac p₁ p₂ p₅)

    f-ext : Extensional f
    f-ext = fst (snd (eac p₁ p₂ p₅))

    S₁ : Subset S _
    S₁ x = ∃[ j ⦂ I ] f j ≍ x

    p₆ : Extensional-≍-↔ S₁
    p₆ x≍y = (λ { (j , fj≍x) → j , ≍-trans {S = S} fj≍x x≍y })
           , (λ { (j , fj≍y) → j , ≍-trans {S = S} fj≍y (≍-sym {S = S} x≍y) })

    f-common : ∀ i → (A i ∩ S₁) (f i)
    f-common i = snd (snd (eac p₁ p₂ p₅)) i , i , ≍-refl {S = S}

    f-unique : ∀ i {y} → (A i ∩ S₁) y → f i ≍ y
    f-unique i {y} (y-here , j , fj≍y) = fi≍y
      where
        fj-there : A j (f j)
        fj-there = fst (f-common j)

        y-there : A j y
        y-there = fst (p₁ fj≍y) fj-there

        i≍j : i ≍ j
        i≍j = p₃ y-here y-there

        fi≍y : f i ≍ y
        fi≍y = ≍-trans {S = S} (f-ext i≍j) fj≍y

    p₇ : ∀ i → ∃![ x ⦂ S ] (A i ∩ S₁) x
    p₇ i = f i , f-common i , f-unique i
```
:::


#### Theorem I.

*The following are equivalent in constructive type theory:*

i.    *The exten&shy;sional axiom of choice.*
ii.   *Zermelo’s axiom of choice.*
iii.  *Epimorphisms split, that is, every surjective exten&shy;sional function has an
      exten&shy;sional right inverse.*
iv.   *Unique representatives can be picked from the equivalence classes of any given equivalence
      relation.*

Of these four equivalent statements, (iii) is the topos-theoretic axiom of choice, which is thus
equivalent, not to the constructively valid type-theoretic axiom of choice, but to Zermelo’s axiom
of choice.

##### Proof.

We shall prove the implications (i)$→$(ii)$→$(iii)$→$(iv)$→$(i) in this order.

###### (i)$→$(ii).

::: {.align}
This is precisely the result of the considerations prior to the formulation of the theorem.

```
i→ii : ∀ {ℓ} → EAC ℓ → ZAC ℓ
i→ii = eac→zac
```
:::

###### (ii)$→$(iii).

::: {.align}
Let $(S, ≍_S)$ and $(I, ≍_I)$ be two exten&shy;sional sets, and let $f : S → I$ be an
exten&shy;sional and surjective mapping between them.  By definition, put

$$A_i = f^{-1}(i) = \{x\ |\ f(x) ≍_I i\}.$$

Then

1.  $x ≍_S y → (A_i(x) ↔ A_i(y))$

by the assumed exten&shy;sionality of $f,$

2.  $i ≍_I j → (∀x : S)(A_i(x) ↔ A_j(x))$

since $f(x) ≍_I i$ is equivalent to $f(x) ≍_I j$ provided that $i ≍_I j,$

3.  $(∃x : S)(A_i(x) ∧ A_j(x)) → i ≍_I j$

since $f(x) ≍_I i$ and $f(x) ≍_I j$ together imply $i ≍_I j,$

4.  $(∀x : S)(∃i : I)A_i(x)$

since $A_{f(x)}(x)$ for any $x : S,$ and

5.  $(∀i : I)(∃x : S)A_i(x)$

by the assumed surjectivity of the function $f.$  Therefore we can apply Zermelo’s axiom of choice
to get a subset $S_1$ of $S$ such that

$$(∀i : I)(∃!x : S)(A_i ∩ S_1)(x).$$

The constructive, or inten&shy;sional, axiom of choice, to which we have access in type theory, then
yields $g : I → S$ such that $(A_i ∩ S_1)(g(i)),$ that is,

$$(f(g(i)) ≍_I i) ∧ S_1(g(i)),$$

so that $g$ is a right inverse of $f,$ and

$$(A_i ∩ S_1)(y) → g(i) ≍_S y.$$

It remains only to show that $g$ is exten&shy;sional.  So assume $i, j : I.$  Then we have

$$(A_i ∩ S_1)(g(i))$$

as well as

$$(A_j ∩ S_1)(g(j))$$

so that, if also $i ≍_I j,$

$$(A_i ∩ S_1)(g(j))$$

by the exten&shy;sional dependence of $A_i$ on the index $i.$  The uniqueness property of
$A_i ∩ S_1$ permits us to now conclude $g(i) ≍_S g(j)$ as desired.

```
Surjective : ∀ {𝓈 𝓉 ℯT} {S : Set 𝓈} {T : Set 𝓉} (f : S → T)
               {{≍T : Equivalence T ℯT}} → Set _
Surjective {S = S} f = ∀ y → ∃[ x ⦂ S ] f x ≍ y

RightInverse : ∀ {𝓈 𝓉 ℯT} {S : Set 𝓈} {T : Set 𝓉} (g : T → S) (f : S → T)
                 {{≍T : Equivalence T ℯT}} → Set _
RightInverse g f = ∀ y → (f ∘ g) y ≍ y

-- every surjective extensional function has an extensional right inverse
AC₃ : ∀ ℓ → Set _
AC₃ ℓ = ∀ {I S : Set ℓ} (f : S → I)
          {{≍I : Equivalence I ℓ}} {{≍S : Equivalence S ℓ}}
          (f-ext : Extensional f) (f-surj : Surjective f) →
        ∃[ g ⦂ (I → S) ] RightInverse g f ∧ Extensional g

ii→iii : ∀ {ℓ} → ZAC ℓ → AC₃ ℓ
ii→iii zac {I} {S} f f-ext f-surj = g , g-f-rinv , g-ext
  where
    A : I → Subset S _
    A i x = f x ≍ i

    p₁ : Extensional-≍S-↔ A
    p₁ x≍y = (λ fx≍i → ≍-trans {S = I} (≍-sym {S = I} (f-ext x≍y)) fx≍i)
           , (λ fy≍i → ≍-trans {S = I} (f-ext x≍y) fy≍i)

    p₂ : Extensional-≍I-↔ A
    p₂ i≍j = (λ fx≍i → ≍-trans {S = I} fx≍i i≍j)
           , (λ fx≍j → ≍-trans {S = I} fx≍j (≍-sym {S = I} i≍j))

    p₃ : MutuallyExclusive A
    p₃ fx≍i fx≍j = ≍-trans {S = I} (≍-sym {S = I} fx≍i) fx≍j

    p₄ : Exhaustive A
    p₄ x = f x , ≍-refl {S = I}

    p₅ : Nonempty A
    p₅ = f-surj

    S₁ : Subset S _
    S₁ = fst (zac p₁ p₂ p₃ p₄ p₅)

    g : I → S
    g = fst (ac (snd (snd (zac p₁ p₂ p₃ p₄ p₅))))

    g-common : ∀ i → (A i ∩ S₁) (g i)
    g-common i = fst (snd (ac (snd (snd (zac p₁ p₂ p₃ p₄ p₅)))) i)

    g-unique : ∀ i {y} → (A i ∩ S₁) y → g i ≍ y
    g-unique i = snd (snd (ac (snd (snd (zac p₁ p₂ p₃ p₄ p₅)))) i)

    g-f-rinv : RightInverse g f
    g-f-rinv i = fst (g-common i)

    g-ext : Extensional g
    g-ext {i} {j} i≍j = gi≍gj
      where
        gj-there : (A j ∩ S₁) (g j)
        gj-there = g-common j

        gj-here : (A i ∩ S₁) (g j)
        gj-here = snd (p₂ i≍j) (fst gj-there) , snd gj-there

        gi≍gj : g i ≍ g j
        gi≍gj = g-unique i gj-here
```
:::

###### (iii)$→$(iv).

::: {.align}
Let $I$ be a set equipped with an equivalence relation $≍_I.$  Then the identity function on $I$ is
an exten&shy;sional surjection from $(I, \text{Id}_I)$ to $(I, ≍_I),$ since any function is
exten&shy;sional with respect to the identity relation.  Assuming that epimorphisms split, we can
conclude that there exists a function $g : I → I$ such that

$$g(i) ≍_I i$$

and

$$i ≍_I j → \text{Id}_I(g(i), g(j)),$$

which is to say that $g$ has the miraculous property of picking a unique representative from each
equivalence class of the given equivalence relation $≍_I.$

```
ext-Id→≍ : ∀ {𝓈 𝓉 ℯT} {S : Set 𝓈} {T : Set 𝓉} (f : S → T)
              {{≍T : Equivalence T ℯT}} → Extensional-Id-≍ f
ext-Id→≍ f refl = ≍-refl

id-surj : ∀ {𝓈 ℯS} {S : Set 𝓈}
            {{≍S : Equivalence S ℯS}} → Surjective id
id-surj y = y , ≍-refl

-- every equivalence class of any equivalence relation has a unique representative
AC₄ : ∀ ℓ → Set _
AC₄ ℓ = ∀ {I : Set ℓ}
          {{≍I : Equivalence I ℓ}} →
        ∃[ g ⦂ (I → I) ] RightInverse g id ∧ Extensional-≍-Id g

iii→iv : ∀ {ℓ} → AC₃ ℓ → AC₄ ℓ
iii→iv ac₃ = ac₃ id {{≍S = Id-≍}} (ext-Id→≍ id) id-surj
```
:::

###### (iv)$→$(i).

::: {.align}
Let $(I, ≍_I)$ and $(S, ≍_S)$ be two sets, each equipped with an equivalence relation, and let
$(A_i)_{i : I}$ be a family of exten&shy;sional subsets of $S,$

$$x ≍_S y → (A_i(x) ↔ A_i(y)),$$

which depends exten&shy;sionally on the index $i,$

$$i ≍_I j → (∀x : S)(A_i(x) ↔ A_j(x)).$$

Furthermore, assume that

$$(∀i : I)(∃x : S)A_i(x)$$

holds.  By the inten&shy;sional axiom of choice, valid in constructive type theory, we can conclude
that there exists a choice function $f : I → S$ such that

$$(∀i : I)A_i(f(i)).$$

This choice function need not be exten&shy;sional, of course, unless $≍_I$ is the identity relation
on the index set $I.$  But, applying the miraculous principle of picking a unique representative of
each equivalence class to the equivalence relation $≍_I,$ we get a function $g : I → I$ such that

$$g(i) ≍_I i$$

and

$$i ≍_I j → \text{Id}_I(g(i), g(j)).$$

Then $f \circ g : I → S$ becomes exten&shy;sional,

$$
  i ≍_I j → \text{Id}_I(g(i), g(j)) → \underbrace{f(g(i))}_{(f \circ g)(i)}
    ≍_S \underbrace{f(g(j))}_{(f \circ g)(j)}.
$$

Moreover, from $(∀i : I)$$A_i(f(i)),$ it follows that

$$(∀i : I)A_{g(i)}(f(g(i))).$$

But

$$g(i) ≍_I i → (∀x : S)(A_{g(i)}(x) ↔ A_i(x)),$$

so that

$$(∀i : I)A_i(\underbrace{f(g(i))}_{(f \circ g)(i)}).$$

::: {.qed}
Hence $f \circ g$ has become an exten&shy;sional choice function, which means that the
exten&shy;sional axiom of choice is satisfied.
:::

```
iv→i : ∀ {ℓ} → AC₄ ℓ → EAC ℓ
iv→i ac₄ {I} {S} {A} p₁ p₂ p₅ = f ∘ g , f∘g-ext , f∘g-common
  where
    f : I → S
    f = fst (ac p₅)

    f-common : ∀ i → A i (f i)
    f-common = snd (ac p₅)

    g : I → I
    g = fst ac₄

    g-id-rinv : RightInverse g id
    g-id-rinv = fst (snd ac₄)

    g-ext : Extensional-≍-Id g
    g-ext = snd (snd ac₄)

    f∘g-ext : Extensional (f ∘ g)
    f∘g-ext i≍j = Id→≍ (cong f (g-ext i≍j))

    f∘g-common : ∀ i → A i ((f ∘ g) i)
    f∘g-common i = fst (p₂ (g-id-rinv i)) (f-common (g i))

theorem-i : ∀ {𝓁} → (EAC 𝓁 → ZAC 𝓁) ∧ (ZAC 𝓁 → AC₃ 𝓁) ∧ (AC₃ 𝓁 → AC₄ 𝓁) ∧ (AC₄ 𝓁 → EAC 𝓁)
theorem-i = i→ii , ii→iii , iii→iv , iv→i
```
:::

Another indication that the exten&shy;sional axiom of choice is the correct type-theoretic
rendering of Zermelo’s axiom of choice comes from constructive set theory.  Peter Aczel has shown
how to interpret the language of Zermelo-Fraenkel set theory in constructive type theory, this
interpretation being the natural constructive version of the cumulative hierarchy, and investigated
what set-theoretic principles that become validated under that interpretation.[^17]  But one may
also ask, conversely, what principle, or principles, that have to be adjoined to constructive type
theory in order to validate a specific set-theoretic axiom.  In particular, this may be asked about
the formalised version of the axiom of choice that Zermelo made part of his own axiomatisation of
set theory.  The answer is as follows.


#### Theorem II.

*When constructive type theory is strengthened by the exten&shy;sional axiom of choice, the
set-theoretic axiom of choice becomes validated under the Aczel interpretation.*

##### Proof.

::: {.align}
The set-theoretic axiom of choice says that, for any two iterative sets $α$ and $β$ and any
relation $R$ between iterative sets,

$$(∀x ∈ α)(∃y ∈ β)R(x, y) → (∃φ : α → β)(∀x ∈ α)R(x, φ(x)).$$

The Aczel interpretation of the left-hand member of this implication is

$$(∀x : ᾱ)(∃y : β̄)R(α̃(x), β̃(x)),$$

which yields

$$(∃f : ᾱ → β̄)(∀x : ᾱ)R(α̃(x), β̃(f (x)))$$

by the type-theoretic axiom of choice.  Now, put

$$φ = \{⟨α̃(x), β̃(f(x))⟩\ |\ x : ᾱ\}$$

by definition.  We need to prove that $φ$ is a function from $α$ to $β$ in the sense of
constructive set theory, that is,

$$α̃(x) = α̃(x') → β̃(f(x)) = β̃(f(x')).$$

Define the equivalence relations

$$(x ≍_{ᾱ} x') = (α̃(x) = α̃(x'))$$

and

$$(y ≍_{β̄} y') = (β̃(y) = β̃(y'))$$

on $ᾱ$ and $β̄,$ respectively.  By the exten&shy;sional axiom of choice in type theory, the choice
function $f : ᾱ → β̄$ can be taken to be exten&shy;sional with respect to these two equivalence
relations,

$$x ≍_{ᾱ} x' → f(x) ≍_{β̄} f(x'),$$

::: {.qed}
which ensures that $φ,$ defined as above, is a function from $α$ to $β$ in the sense of
constructive set theory.
:::

```
-- TODO
```
:::


#### Corollary.

*When constructive type theory (including one universe and the $W$-operation) is strengthened by
the exten&shy;sional axiom of choice, it interprets all of ZFC.*

##### Proof.

::: {.qed}
We already know from Aczel that ZF is equivalent to CZF $+$ EM.[^18]  Hence ZFC is equivalent to CZF
$+$ EM $+$ AC.  But, by Diaconescu’s theorem as transferred to constructive set theory by Goodman
and Myhill, the law of excluded middle follows from the axiom of choice in the context of
constructive set theory.[^19]  It thus suffices to interpret CZF $+$ AC in CTT $+$ ExtAC, and this
is precisely what the Aczel interpretation does, by the previous theorem.
:::

Another way of reaching the same conclusion is to interchange the order of the last two steps in
the proof just given, arguing instead that ZFC $=$ CZF $+$ EM $+$ AC is interpretable in CTT $+$ EM
$+$ ExtAC by the previous theorem, and then appealing to the type-theoretic version of Diaconescu’s
theorem, according to which the law of excluded middle follows from the exten&shy;sional axiom of
choice in the context of constructive type theory.[^20]  The final conclusion is anyhow that ZFC is
interpretable in CTT $+$ ExtAC.

::: {.align}
When Zermelo’s axiom of choice is formulated in the context of constructive type theory instead of
Zermelo-Fraenkel set theory, it appears as ExtAC, the exten&shy;sional axiom of choice

$$(∀i : I)(∃x : S)A(i, x) → (∃f : I → S)(\text{Ext}(f) ∧ (∀i : I)A(i, f(i))),$$

where

$$\text{Ext}(f) = (∀i, j : I)(i ≍_I j → f(i) ≍_S f(j)),$$

and it then becomes manifest what is the problem with it: it breaks the principle that you cannot
get something from nothing.  Even if the relation $A(i, x)$ is exten&shy;sional with respect to its
two arguments, the truth of the antecedent $(∀i : I)$$(∃x : S)$$A(i, x),$ which does guarantee the
existence of a choice function $f : I → S$ satisfying $(∀i : I)$$A(i, f(i)),$ is not enough to
guarantee the exten&shy;sionality of the choice function, that is, the truth of Ext$(f).$
Thus the problem with Zermelo’s axiom of choice is not the existence of the choice function but its
exten&shy;sionality, and this is not visible within an exten&shy;sional framework, like
Zermelo-Fraenkel set theory, where all functions are by definition exten&shy;sional.

If we want to ensure the exten&shy;sionality of the choice function, the antecedent clause of the
exten&shy;sional axiom of choice has to be strengthened.  The natural way of doing this is to
replace ExtAC by AC!, the axiom of unique choice, or no choice,

$$(∀i : I)(∃!x : S)A(i, x) → (∃f : I → S)(\text{Ext}(f) ∧ (∀i : I)A(i, f(i))),$$

which is as valid as the inten&shy;sional axiom of choice.  Indeed, assume
$(∀i : I)$$(∃!x : S)$$A(i, x)$ to be true.  Then, by the inten&shy;sional axiom of choice, there
exists a choice function $f : I → S$ satisfying $(∀i : I)$$A(i, f(i)).$  Because of the uniqueness
condition, such a function $f : I → S$ is necessarily exten&shy;sional.  For suppose that
$i, j : I$ are such that $i ≍_I j$ is true.  Then $A(i, f(i))$ and $A(j, f(j))$ are both true.
Hence, by the exten&shy;sionality of $A(i, x)$ in its first argument, so is $A(i, f(j)).$  The
uniqueness condition now guarantees that $f(i) ≍_S f(j),$ that is, that $f : I → S$ is
exten&shy;sional.  The axiom of unique choice AC! may be considered as the valid form of
exten&shy;sional choice, as opposed to ExtAC, which lacks justification.

```
-- axiom of unique choice
AC! : ∀ ℓ → Set _
AC! ℓ = ∀ {I S : Set ℓ} {A : I → Subset S ℓ}
          {{≍I : Equivalence I ℓ}} {{≍S : Equivalence S ℓ}}
          (p₁ : Extensional-≍S-↔ A) (p₂ : Extensional-≍I-↔ A) →
        (∀ i → ∃![ x ⦂ S ] A i x) → ∃[ f ⦂ (I → S) ] Extensional f ∧ ∀ i → A i (f i)

ac! : ∀ {ℓ} → AC! ℓ
ac! {I = I} {S} {A} p₁ p₂ h = f , f-ext , f-common
  where
    f : I → S
    f = fst (ac h)

    f-common : ∀ i → A i (f i)
    f-common i = fst (snd (ac h) i)

    f-unique : ∀ i {y} → A i y → f i ≍ y
    f-unique i = snd (snd (ac h) i)

    f-ext : Extensional f
    f-ext {i} {j} i≍j = fi≍fj
      where
        fj-there : A j (f j)
        fj-there = f-common j

        fj-here : A i (f j)
        fj-here = fst (p₂ (≍-sym {S = I} i≍j)) fj-there

        fi≍fj : f i ≍ f j
        fi≍fj = f-unique i fj-here
```
:::

The inability to distinguish between the inten&shy;sional and the exten&shy;sional axiom of choice
has led to one’s taking the need for the axiom of choice in proving that the union of a countable
sequence of countable sets is again countable, that the real numbers, defined as Cauchy sequences of
rational numbers, are Cauchy complete, etc., as a justification of Zermelo’s axiom of choice.  As
Zermelo himself wrote towards the end of the short paper in which he originally introduced the axiom
of choice,

> [Dieses logische Prinzip läßt sich zwar nicht auf ein noch einfacheres zurückführen, wird aber in
> der mathematischen Deduktion überall unbedenklich angewendet.]{lang=de}[^21]

What Zermelo wrote here about the omnipresent, and often subconscious, use of the axiom of choice in
mathematical proofs is incontrovertible, but it concerns the constructive, or inten&shy;sional,
version of it, which follows almost immediately from the strong rule of existential elimination.  It
cannot be taken as a justification of his own version of the axiom of choice, including as it does
the exten&shy;sionality of the choice function.

Within an exten&shy;sional foundational framework, like topos theory or constructive set theory, it
is not wholly impossible to formulate a counterpart of the constructive axiom of choice, despite of
its inten&shy;sional character, but it becomes complicated.  In topos theory, there is the axiom
that there are enough projectives, which is to say that every object is the surjective image of a
projective object, and, in constructive set theory, Aczel has introduced the analogous axiom that
every set has a base.[^22]  Roughly speaking, this is to say that every set is the surjective image
of a set for which the axiom of choice holds.  The technical complication of these axioms speaks to
my mind for an inten&shy;sional foundational framework, like constructive type theory, in which the
intuitive argument why the axiom of choice holds on the Brouwer-Heyting-Kolmogorov interpretation is
readily formalized, and in which whatever exten&shy;sional notions that are needed can be built up,
in agreement with the title of Martin Hofmann’s thesis, *Exten&shy;sional Constructs in
Inten&shy;sional Type Theory*.[^23]  Exten&shy;sionality does not come for free.

Finally, since this is only a couple of weeks from the centenary of Zermelo’s first formulation of
the axiom of choice, it may not be out of place to remember the crucial role it has played for the
formalisation of both Zermelo-Fraenkel set theory and constructive type theory.  In the case of set
theory, there was the need for Zermelo of putting his proof of the well-ordering theorem on a
formally rigorous basis, whereas, in the case of type theory, there was the intuitively convincing
argument which made axiom of choice evident on the constructive interpretation of the logical
operations, an argument which nevertheless could not be faithfully formalised in any then existing
formal system.


[^1]:  G. Cantor (1883) [[Über unendliche lineare Punktmannigfaltigkeiten.  Nr. 5]{lang=de}
       ](https://sci-hub.st/10.1007/BF01446819),
       *[Math. Annalen]{lang=de}*, Vol. 21(4), pp. 545–591.
       Reprinted in *[[Gesammelte Abhandlungen]{lang=de}
       ](https://sci-hub.st/10.1007/978-3-662-00274-2)*,
       Edited by E. Zermelo (1932), Springer, Berlin, pp. 165–208.

[^2]:  G. H. Moore (1982) *[Zermelo’s Axiom of Choice: Its Origins, Development, and Influence
       ](https://sci-hub.st/10.1007/978-1-4613-9478-5)*,
       Springer, New York, p. 51.

[^3]:  E. Zermelo (1904) [[Beweis, daß jede Menge wohlgeordnet werden kann.  (Aus einem an Herrn
       Hilbert gerichteten Briefe.)]{lang=de}](https://sci-hub.st/10.1007/BF01445300),
       *[Math. Annalen]{lang=de}*, Vol. 59(4), pp. 514–516.

[^4]:  E. Zermelo (1908) [[Neuer Beweis für die Möglichkeit einer Wohlordnung]{lang=de}
       ](https://sci-hub.st/10.1007/BF01450054),
       *[Math. Annalen]{lang=de}*, Vol. 65(1), pp. 107–128.

[^5]:  E. Zermelo (1908) [[Untersuchungen über die Grundlagen der Mengenlehre.  I]{lang=de}
       ](https://sci-hub.st/10.1007/BF01449999),
       *[Math. Annalen]{lang=de}*, Vol. 65(2), pp. 261–281.

[^6]:  G. H. Moore (1982), [op. cit.](#fn2), pp. 92–137.

[^7]:  M. Zorn (1935) [A remark on method in transfinite algebra
       ](https://sci-hub.st/10.1090/S0002-9904-1935-06166-X),
       *Bull. Amer. Math. Soc.*, Vol. 41(10), pp. 667–670.

[^8]:  R. Baire, É. Borel, J. Hadamard, and H. Lebesgue (1905) [[Cinq lettres sur la théorie des
       ensembles]{lang=fr}](http://www.numdam.org/item/10.24033/bsmf.761.pdf),
       *[Bull. Soc. Math. France]{lang=fr}*, Vol. 33(17), pp. 261–273.

[^9]:  É. Borel (1905) [[Quelques remarques sur les principes de la théorie des ensembles]{lang=fr}
       ](https://sci-hub.st/10.1007/BF01677266),
       *[Math. Annalen]{lang=de}*, Vol. 60(2), pp. 194–195.

[^10]: L. E. J. Brouwer (1907) *[[Over de Grondslagen der Wiskunde]{lang=nl}
       ](https://eprints.illc.uva.nl/id/eprint/1852/2/HDS-20-LEJBrouwer.text.pdf)*,
       Maas \& van Suchtelen, Amsterdam.
       English translation in *[Collected Works, Vol. 1
       ](https://library.lol/main/0CFBA75A5C78E49F96114337B2B8790D)*,
       Edited by A. Heyting (1975), North-Holland, Amsterdam, pp. 11–101.

[^11]: E. Bishop (1967) *[Foundations of Constructive Analysis
       ](https://library.lol/main/D69762DE514CE40FAA389C6F178F66D4)*,
       McGraw-Hill, New York, p. 9.

[^12]: R. Diaconescu (1975) [Axiom of choice and complementation
       ](https://sci-hub.st/10.1090/S0002-9939-1975-0373893-X),
       *Proc. Amer. Math. Soc.*, Vol. 51(1), pp. 176–178.

[^13]: E. Zermelo (1904), [op. cit.](#fn3), footnote 3, p. 514.

[^14]: E. Zermelo (1908), [op. cit.](#fn4), footnote 4, p. 110.

[^15]: A. N. Whitehead (1902) [On cardinal numbers](https://sci-hub.st/10.2307/2370026),
       *Amer. J. Math.*, Vol. 24(4), pp. 367–394.

[^16]: B. Russell (1906) [On some difficulties in the theory of transfinite numbers and order types
       ](https://sci-hub.st/10.1112/plms/s2-4.1.29),
       *Proc. London Math. Soc.*, Ser. 2, Vol. 4(1), pp. 29–53.

[^17]: P. Aczel (1978) [The type-theoretic interpretation of constructive set theory
       ](mi.Aczel1978.html){.mi},
       *Logic Colloquium ’77*, Edited by A. Macintyre, L. Pacholski, and J. Paris, North-Holland,
       Amsterdam, pp. 55–66.

[^18]: P. Aczel (1978), [op. cit.](#fn17), p. 59.

[^19]: N. D. Goodman and J. Myhill (1978) [Choice implies excluded middle
       ](https://sci-hub.st/10.1002/malq.19780242514),
       *[Zeitschrift für math. Logik und Grundlagen der Math.]{lang=de}*, Vol. 24(25–30), p. 461.

[^20]: S. Lacas and B. Werner (1999) ~~Which choices imply the excluded middle? About Diaconescu’s
       trick in type theory~~,
       Unpublished, pp. 9–10.
       I am indebted to Jesper Carlström for providing me with this reference.

[^21]: E. Zermelo (1904), [op. cit.](#fn3), footnote 3, p. 516.

[^22]: P. Aczel (1982) [The type-theoretic interpretation of constructive set theory: Choice
       principles](https://sci-hub.st/10.1016/S0049-237X(09)70120-X),
       *L. E. J. Brouwer Centenary Symposium*, Edited by A. S. Troelstra and D. van Dalen,
       North-Holland, Amsterdam, 1982, pp. 1–40.

[^23]: M. Hofmann (1997) *[Exten&shy;sional Constructs in Inten&shy;sional Type Theory
       ](https://sci-hub.st/10.1007/978-1-4471-0963-1)*,
       Springer, London.
