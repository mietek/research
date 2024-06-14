```
{-# OPTIONS --allow-unsolved-metas #-}

module AC where

open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; Σ-syntax)
open import Function using (_∘_)
open import Level using (_⊔_ ; suc)
open import Relation.Binary using (Setoid)
open import Relation.Unary using (_∩_)

_↔_ : ∀ {𝓈 𝓉} (S : Set 𝓈) (T : Set 𝓉) → Set _
S ↔ T = (S → T) × (T → S)

Σ!-syntax : ∀ {𝓈 𝓈₌ 𝓉} (S : Set 𝓈) (_=S_ : S → S → Set 𝓈₌) (T : S → Set 𝓉) → Set _
Σ!-syntax S _=S_ T = Σ[ x ∈ S ] T x × ∀ y → T y → x =S y

infix 2 Σ!-syntax
syntax Σ!-syntax S _=S_ (λ x → T) = Σ![ x ∈ S / _=S_ ] T

drop! : ∀ {𝓈 𝓈₌ 𝓉} {S : Set 𝓈} {_=S_ : S → S → Set 𝓈₌} {T : S → Set 𝓉} →
        Σ![ x ∈ S / _=S_ ] T x → Σ[ x ∈ S ] T x
drop! (x , t , h) = x , t
```
--------------------------------------------------------------------------------

# 100 years of Zermelo’s axiom of choice: what was the problem with it?

## Per Martin-Löf

Cantor conceived set theory in a sequence of six papers published in the
*Mathematische Annalen* during the five year period 1879–1884.  In the fifth of
these papers, published in 1883,[^1] he stated as a law of thought (Denkgesetz)
that every set can be well-ordered or, more precisely, that it is always
possible to bring any well-defined set into the form of a well-ordered set.
Now to call it a law of thought was implicitly to claim self-evidence for it,
but he must have given up that claim at some point, because in the 1890’s he
made an unsuccessful attempt at demonstrating the well-ordering principle.[^2]

The first to succeed in doing so was Zermelo,[^3] although, as a prerequisite of
the demonstration, he had to introduce a new principle, which came to be called
the principle of choice (Prinzip der Auswahl) respectively the axiom of choice
(Axiom der Auswahl) in his two papers from 1908.[^4] [^5]  His first paper on
the subject, published in 1904, consists of merely three pages, excerpted by
Hilbert from a letter which he had received from Zermelo.  The letter is dated
24 September 1904, and the excerpt begins by saying that the demonstration came
out of discussions with Erhard Schmidt during the preceding week, which means
that we can safely date the appearance of the axiom of choice and the
demonstration of the well-ordering theorem to September 1904.

Brief as it was, Zermelo’s paper gave rise to what is presumably the most lively
discussion among mathematicians on the validity, or acceptability, of a
mathematical axiom that has ever taken place.  Within a couple of years, written
contributions to this discussion had been published by Felix Bernstein,
Schoenflies, Hamel, Hessenberg and Hausdorff in Germany, Baire, Borel, Hadamard,
Lebesgue, Richard and Poincaré in France, Hobson, Hardy, Jourdain and Russell in
England, Julius König in Hungary, Peano in Italy and Brouwer in the
Netherlands.[^6]  Zermelo responded to those of these contributions that were
critical, which was a majority, in a second paper from 1908.  This second paper
also contains a new proof of the well-ordering theorem, less intuitive or less
perspicuous, it has to be admitted, than the original proof, as well as a new
formulation of the axiom of choice, a formulation which will play a crucial role
in the following considerations.

Despite the strength of the initial opposition against it, Zermelo’s axiom of
choice gradually came to be accepted mainly because it was needed at an early
stage in the development of several branches of mathematics, not only set
theory, but also topology, algebra and functional analysis, for example.
Towards the end of the thirties, it had become firmly established and was made
part of the standard mathematical curriculum in the form of Zorn’s lemma.[^7]

The intuitionists, on the other hand, rejected the axiom of choice from the very
beginning, Baire, Borel and Lebesgue were all critical of it in their
contributions to the correspondence which was published under the title «Cinq
lettres sur la théorie des ensembles» in 1905.[^8]  Brouwer’s thesis from 1907
contains a section on the well-ordering principle in which is treated in a
dismissive fashion (“of course there is no motivation for this at all”) and in
which, following Borel,[^9] he belittles Zermelo’s proof of it from the axiom of
choice.[^10]  No further discussion of the axiom of choice seems to be found in
either Brouwer’s or Heyting’s writings.  Presumably, it was regarded by them as
a prime example of a nonconstructive principle.

It therefore came as a surprise when, as late as in 1967, Bishop stated,

<blockquote>
A choice function exists in constructive mathematics, because a choice is
*implied by the very meaning of existence,*[^11]
</blockquote>

although, in the terminology that he himself introduced in the subsequent
chapter, he ought to have said “choice operation” rather than “choice function”.
What he had in mind was clearly that the truth of

$$(∀i : I)(∃x : S)A(i, x) → (∃f : I → S)(∀i : I)A(i, f(i))$$

and even, more generally,

$$(∀i : I)(∃x : S_i)A(i, x) → (∃f : Π_{i : I} S_i)(∀i : I)A(i, f(i))$$

becomes evident almost immediately upon remembering the
Brouwer-Heyting-Kolmogorov interpretation of the logical constants, which means
that it might as well have been observed already in the early thirties.  And it
is this intuitive justification that was turned into a formal proof in
constructive type theory, a proof that effectively uses the strong rule of
$∃$-elimination that it became possible to formulate as a result of having made
the proof objects appear in the system itself and not only in its
interpretation.

--------------------------------------------------------------------------------
```
module _ {𝒾} {I : Set 𝒾} where
  module _ {𝓈 𝒶} {S : Set 𝓈} {A : I → S → Set 𝒶} where
    -- (constructive, intensional, type-theoretic) axiom of choice
    AC : Set _
    AC = (∀ i → Σ[ x ∈ S ] A i x) → Σ[ f ∈ (I → S) ] ∀ i → A i (f i)

    ac : AC
    ac h = proj₁ ∘ h , proj₂ ∘ h

  module _ {𝓈 𝒶} {S : I → Set 𝓈} {A : ∀ i → S i → Set 𝒶} where
    -- dependent (constructive, intensional, type-theoretic) axiom of choice
    DepAC : Set _
    DepAC = (∀ i → Σ[ x ∈ S i ] A i x) → Σ[ f ∈ (∀ i → S i) ] ∀ i → A i (f i)

    depac : DepAC
    depac h = proj₁ ∘ h , proj₂ ∘ h
```
--------------------------------------------------------------------------------

In 1975, soon after Bishop’s vindication of the constructive axiom of choice,
Diaconescu proved that, in topos theory, the law of excluded middle follows from
the axiom of choice.[^12]  Now, topos theory being an intuitionistic theory,
albeit impredicative, this is on the surface of it incompatible with Bishop’s
observation because of the constructive inacceptability of the law of excluded
middle.  There is therefore a need to investigate how the constructive axiom of
choice, validated by the Brouwer-Heyting-Kolmogorov interpretation, is related
to Zermelo’s axiom of choice on the one hand and to the topos-theoretic axiom
of choice on the other.

To this end, using constructive type theory as our instrument of analysis, let
us simply try to prove Zermelo’s axiom of choice.  This attempt should of course
fail, but in the process of making it we might at least be able to discover what
it is that is really objectionable about it.  So what was Zermelo’s axiom of
choice?  In the original paper from 1904, he gave to it the following
formulation,

<blockquote>
*Jeder Teilmenge $M'$ denke man sich ein beliebiges Element $m'_1$ zugeordnet,
das in $M'$ selbst vorkommt und das „ausgezeichnete” Element von $M'$ genannt
werden möge.*[^13]
</blockquote>

Here $M'$ is an arbitrary subset, which contains at least one element, of a
given set $M$.  What is surprising about this formulation is that there is
nothing objectionable about it from a constructive point of view.  Indeed, the
distinguished element $m'_1$ can be taken to be the left projection of the proof
of the existential proposition $(∃x : M)M'(x)$, which says that the subset $M'$
of $M$ contains at least one element.  This means that one would have to go into
the demonstration of the well-ordering theorem in order to determine exactly
what are its nonconstructive ingredients.

Instead of doing that, I shall turn to the formulation of the axiom of choice
that Zermelo favoured in his second paper on the well-ordering theorem from
1908,

<blockquote>
*Axiom.  Eine Menge $S$, welche in eine Menge getrennter Teile $A, B, C, …$
zerfällt, deren jeder mindestens ein Element enthält, besitzt mindestens eine
Untermenge $S_1$, welche mit jedem der betrachteten Teile $A, B, C, …$ genau
ein Element gemein hat.*[^14]
</blockquote>

Formulated in this way, Zermelo’s axiom of choice turns out to coincide with the
multiplicative axiom, which Whitehead and Russell had found indispensable for
the development of the theory of cardinals.[^15] [^16]  The type-theoretic
rendering of this formulation of the axiom of choice is straightforward, once
one remembers that a basic set in the sense of Cantorian set theory corresponds
to an extensional set, that is, a set equipped with an equivalence relation, in
type theory, and that a subset of an extensional set is interpreted as a
propositional function which is extensional with respect to the equivalence
relation in question.  Thus the data of Zermelo’s 1908 formulation of the axiom
of choice are a set $S$, which comes equipped with an equivalence relation
$=_S$, and a family $(A_i)_{i : I}$ of propositional functions on $S$ satisfying
the following properties,

1.  $x =_S y → (A_i(x) ↔ A_i(y))$ (extensionality),

2.  $i =_I j → (∀x : S)(A_i(x) ↔ A_j(x))$ (extensionality of the dependence on
    the index),

3.  $(∃x : S)(A_i(x) ∧ A_j(x)) → i =_I j$ (mutual exclusiveness),

4.  $(∀x : S)(∃i : I)A_i(x)$ (exhaustiveness),

5.  $(∀i : I)(∃x : S)A_i(x)$ (nonemptiness).

Given these data, the axiom guarantees the existence of a propositional function
$S_1$ on $S$ such that

6.  $x =_S y → (S_1(x) ↔ S_1(y))$ (extensionality),

7.  $(∀i : I)(∃!x : S)(A_i ∩ S_1)(x)$ (uniqueness of choice).

The obvious way of trying to prove (6) and (7) from (1)–(5) is to apply the
type-theoretic (constructive, intensional) axiom of choice to (5), so as to get
a function $f : I → S$ such that

$$(∀i : I)A_i(f(i)),$$

and then define $S_1$ by the equation

$$S_1 = \{f(j)\ |\ j : I\} = \{x\ |\ (∃j : I)(f(j)) =_S x)\}.$$

Defined in this way, $S_1$ is clearly extensional, which is to say that it
satisfies (6).  What about (7)?  Since the proposition

$$(A_i ∩ S_1)(f(i)) = A_i(f(i)) ∧ S_1(f(i))$$

is clearly true, so is

$$(∀i : I)(∃x : S)(A_i ∩ S_1)(x),$$

which means that only the uniqueness condition remains to be proved.  To this
end, assume that the proposition

$$(A_i ∩ S_1)(x) = A_i(x) ∧ S_1(x)$$

is true, that is, that the two propositions

$$
\begin{cases}
  A_i(x),\\
  S_1(x) = (∃j : I)(f(j) =_S x),
\end{cases}
$$

are both true.  Let $j : I$ satisfy $f(j) =_S x$.  Then, since
$(∀i : I)A_i(f(i))$ is true, so is $A_j(f(j))$.  Hence, by the extensionality of
$A_j$ with respect to $=_S$, $A_j(x)$ is true, which, together with the assumed
truth of $A_i(x)$, yields $i =_I j$ by the mutual exclusiveness of the family of
subsets $(A_i)_{i : I}$.  At this stage, in order to conclude that $f(i) =_S x$,
we need to know that the choice function $f$ is extensional, that is, that

$$i =_I j → f(i) =_S f(j).$$

This, however, is not guaranteed by the constructive, or intensional, axiom
of choice which follows from the strong rule of $∃$-elimination in type theory.
Thus our attempt to prove Zermelo’s axiom of choice has failed, as was to be
expected.

On the other hand, we have succeeded in proving that Zermelo’s axiom of choice
follows from the extensional axiom of choice

$$(∀i : I)(∃x : S)A_i(x) → (∃f : I → S)(\text{Ext}(f) ∧ (∀i : I)A_i(f(i))),$$

which I shall call $\text{ExtAC}$, where

$$\text{Ext}(f) = (∀i, j: I)(i =_I j → f(i) =_S f(j)).$$

The only trouble with it is that it lacks the evidence of the intensional axiom
of choice, which does not prevent one from investigating its consequences, of
course.

--------------------------------------------------------------------------------
```
module _ {𝒾 𝒾₌ 𝓈 𝓈₌} (I₌ : Setoid 𝒾 𝒾₌) (S₌ : Setoid 𝓈 𝓈₌) where
  open Setoid I₌ using () renaming (Carrier to I ; _≈_ to _=I_ ; refl to reflI ; sym to symI ; trans to transI)
  open Setoid S₌ using () renaming (Carrier to S ; _≈_ to _=S_ ; refl to reflS ; sym to symS ; trans to transS)

  Ext : ∀ (f : I → S) → Set _
  Ext f = ∀ {i j} → i =I j → f i =S f j

  module _ {𝒶} (A : I → S → Set 𝒶) where
    -- extensional axiom of choice
    ExtAC : Set _
    ExtAC = (∀ i → Σ[ x ∈ S ] A i x) → Σ[ f ∈ (I → S) ] Ext f × ∀ i → A i (f i)

    -- axiom of unique choice
    AC! : Set _
    AC! = (∀ i → Σ![ x ∈ S / _=S_ ] A i x) → Σ[ f ∈ (I → S) ] Ext f × ∀ i → A i (f i)

    extac→ac! : ExtAC → AC!
    extac→ac! extac h = extac (drop! ∘ h)

    record PropertiesOfA : Set (𝒾 ⊔ 𝒾₌ ⊔ 𝓈 ⊔ 𝓈₌ ⊔ 𝒶) where
      field
        extensionality      : ∀ {i x y} → x =S y → (A i x ↔ A i y)
        indexExtensionality : ∀ {i j} → i =I j → ∀ x → (A i x ↔ A j x)
        mutualExclusiveness : ∀ {i j} → (Σ[ x ∈ S ] A i x × A j x) → i =I j
        exhaustiveness      : ∀ x → Σ[ i ∈ I ] A i x
        nonemptiness        : ∀ i → Σ[ x ∈ S ] A i x

    record PropertiesOf {𝓈₁} (S₁ : S → Set 𝓈₁) : Set (𝒾 ⊔ 𝒾₌ ⊔ 𝓈 ⊔ 𝓈₌ ⊔ 𝒶 ⊔ 𝓈₁) where
      field
        extensionality     : ∀ {x y} → x =S y → (S₁ x ↔ S₁ y)
        uniquenessOfChoice : ∀ i → Σ![ x ∈ S / _=S_ ] (A i ∩ S₁) x

    -- Zermelo's axiom of choice
    -- TODO: shouldn't we say that there exists a level 𝓈₁ such that the level
    -- of S₁ is s₁, instead of saying that the level of S₁ is (𝒾 ⊔ 𝓈₌)?
    ZerAC : Set (suc 𝒾 ⊔ 𝒾₌ ⊔ 𝓈 ⊔ suc 𝓈₌ ⊔ 𝒶)
    ZerAC = PropertiesOfA → Σ[ S₁ ∈ (S → Set (𝒾 ⊔ 𝓈₌)) ] PropertiesOf S₁

    zerac : ZerAC
    zerac p₁₋₅ =
      let
        open PropertiesOfA p₁₋₅

        f : I → S
        f = proj₁ (ac nonemptiness)

        S₁ : S → Set _
        S₁ x = Σ[ j ∈ I ] f j =S x

        p₆ : ∀ {x y} → x =S y → (S₁ x ↔ S₁ y)
        p₆ x=y = (λ { (j , fj=x) → j , transS fj=x x=y }) ,
                 (λ { (j , fj=x) → j , transS fj=x (symS x=y) })

        clearlyTrue : ∀ i → (A i ∩ S₁) (f i)
        clearlyTrue i = proj₂ (ac nonemptiness) i , i , reflS

        soIs : ∀ i → Σ[ x ∈ S ] (A i ∩ S₁) x
        soIs i = f i , clearlyTrue i

        Ext[f] : Ext f
        Ext[f] = {!!}

        p₇ : ∀ i → Σ![ x ∈ S / _=S_ ] (A i ∩ S₁) x
        p₇ i = f i , clearlyTrue i , λ { y (Aiy , j , fj=y) →
          let
            Aj[fj] : A j (f j)
            Aj[fj] = proj₁ (clearlyTrue j)

            Ajy : A j y
            Ajy = proj₁ (extensionality fj=y) Aj[fj]

            i=j : i =I j
            i=j = mutualExclusiveness (y , Aiy , Ajy)

            fi=fj : f i =S f j
            fi=fj = Ext[f] i=j

            fi=y : f i =S y
            fi=y = transS fi=fj fj=y
          in
            fi=y }
      in
        S₁ , record { extensionality = p₆ ; uniquenessOfChoice = p₇ }
```
--------------------------------------------------------------------------------

**Theorem I.**  *The following are equivalent in constructive type theory:*

i.    *The extensional axiom of choice.*

ii.   *Zermelo’s axiom of choice.*

iii.  *Epimorphisms split, that is, every surjective extensional function has an
      extensional right inverse.*

iv.   *Unique representatives can be picked from the equivalence classes of any
      given equivalence relation.*

Of these four equivalent statements, (iii) is the topos-theoretic axiom of
choice, which is thus equivalent, not to the constructively valid type-theoretic
axiom of choice, but to Zermelo’s axiom of choice.

*Proof.*  We shall prove the implications (i)→(ii)→(iii)→(iv)→(i) in
this order.

**(i)→(ii).**  This is precisely the result of the considerations prior to the
formulation of the theorem.

<!-- ----------------------------------------------------------------------- -->

**(ii)→(iii).**  Let $(S, =_S)$ and $(I, =_I)$ be two extensional sets, and let
$f : S → I$ be an extensional and surjective mapping between them.  By
definition, put

$$A_i = f^{-1}(i) = \{x\ |\ f(x) =_I i\}.$$

Then

1.  $x =_S y → (A_i(x) ↔ A_i(y))$

by the assumed extensionality of $f$,

2.  $i =_I j → (∀x : S)(A_i(x) ↔ A_j(x))$

since $f(x) =_I i$ is equivalent to $f(x) =_I j$ provided that $i =_I j$,

3.  $(∃x : S)(A_i(x) ∧ A_j(x)) → i =_I j$

since $f(x) =_I i$ and $f(x) =_I j$ together imply $i =_I j$,

4.  $(∀x : S)(∃i : I)A_i(x)$

since $A_{f(x)}(x)$ for any $x : S$, and

5.  $(∀i : I)(∃x : S)A_i(x)$

by the assumed surjectivity of the function $f$.  Therefore we can apply
Zermelo’s axiom of choice to get a subset $S_1$ of $S$ such that

$$(∀i : I)(∃!x : S)(A_i ∩ S_1)(x).$$

The constructive, or intensional, axiom of choice, to which we have access in
type theory, then yields $g : I → S$ such that $(A_i ∩ S_1)(g(i))$, that is,

$$(f(g(i)) =_I i) ∧ S_1(g(i)),$$

so that $g$ is a right inverse of $f$, and

$$(A_i ∩ S_1)(x) → g(i) =_S x.$$

It remains only to show that $g$ is extensional.  So assume $i, j : I$.  Then we
have

$$(A_i ∩ S_1)(g(i))$$

as well as

$$(A_j ∩ S_1)(g(j))$$

so that, if also $i =_I j$,

$$(A_i ∩ S_1)(g(j))$$

by the extensional dependence of $A_i$ on the index $i$.  The uniqueness
property of $A_i ∩ S_1$ permits us to now conclude $g(i) =_S g(j)$ as desired.

<!-- ----------------------------------------------------------------------- -->

**(iii)→(iv).**  Let $I$ be a set equipped with an equivalence relation $=_I$.
Then the identity function on $I$ is an extensional surjection from
$(I, \text{Id}_I)$ to $(I, =_I)$, since any function is extensional with respect
to the identity relation.  Assuming that epimorphisms split, we can conclude
that there exists a function $g : I → I$ such that

$$g(i) =_I i$$

and

$$i =_I j → \text{Id}_I(g(i), g(j)),$$

which is to say that $g$ has the miraculous property of picking a unique
representative from each equivalence class of the given equivalence relation
$=_I$.

<!-- ----------------------------------------------------------------------- -->

**(iv)→(i).**  Let $(I, =_I)$ and $(S, =_S)$ be two sets, each equipped with an
equivalence relation, and let $(A_i)_{i : I}$ be a family of extensional subsets
of $S$,

$$x =_S y → (A_i(x) ↔ A_i(y)),$$

which depends extensionally on the index $i$,

$$i =_I j → (∀x : S)(A_i(x) ↔ A_j(x)).$$

Furthermore, assume that

$$(∀i : I)(∃x : S)A_i(x)$$

holds.  By the intensional axiom of choice, valid in constructive type theory,
we can conclude that there exists a choice function $f : I → S$ such that

$$(∀i : I)A_i(f(i)).$$

This choice function need not be extensional, of course, unless $=_I$ is the
identity relation on the index set $I$.  But, applying the miraculous principle
of picking a unique representative of each equivalence class to the equivalence
relation $=_I$, we get a function $g : I → I$ such that

$$g(i) =_I i$$

and

$$i =_I j → \text{Id}_I(g(i), g(j)).$$

Then $f \circ g : I → S$ becomes extensional,

$$i =_I j → \text{Id}_I(g(i), g(j)) → \underbrace{f(g(i))}_{(f \circ g)(i)}
    =_S \underbrace{f(g(j))}_{(f \circ g)(j)}.$$

Moreover, from $(∀i : I)A_i(f(i))$, it follows that

$$(∀i : I)A_{g(i)}(f(g(i))).$$

But

$$g(i) =_I i → (∀x : S)(A_{g(i)}(x) ↔ A_i(x)),$$

so that

$$(∀i : I)A_i(\underbrace{f(g(i))}_{(f \circ g)(i)}).$$

Hence $f \circ g$ has become an extensional choice function, which means that
the extensional axiom of choice is satisfied.

--------------------------------------------------------------------------------

Another indication that the extensional axiom of choice is the correct
type-theoretic rendering of Zermelo’s axiom of choice comes from constructive
set theory.  Peter Aczel has shown how to interpret the language of
Zermelo-Fraenkel set theory in constructive type theory, this interpretation
being the natural constructive version of the cumulative hierarchy, and
investigated what set-theoretic principles that become validated under that
interpretation.[^17]  But one may also ask, conversely, what principle, or
principles, that have to be adjoined to constructive type theory in order to
validate a specific set-theoretic axiom.  In particular, this may be asked about
the formalized version of the axiom of choice that Zermelo made part of his own
axiomatization of set theory.  The answer is as follows.

**Theorem II.**  *When constructive type theory is strengthened by the
extensional axiom of choice, the set-theoretic axiom of choice becomes validated
under the Aczel interpretation.*

*Proof.*  The set-theoretic axiom of choice says that, for any two iterative
sets $α$ and $β$ and any relation $R$ between iterative sets,

$$(∀x ∈ α)(∃y ∈ β)R(x, y) → (∃φ : α → β)(∀x ∈ α)R(x, φ(x)).$$

The Aczel interpretation of the left-hand member of this implication is

$$(∀x : ᾱ)(∃y : β̄)R(α̃(x), β̃(x)),$$

which yields

$$(∃f : ᾱ → β̄)(∀x : ᾱ)R(α̃(x), β̃(f (x)))$$

by the type-theoretic axiom of choice.  Now, put

$$φ = \{⟨α̃(x), β̃(f(x))⟩\ |\ x : ᾱ\}$$

by definition.  We need to prove that $φ$ is a function from $α$ to $β$ in the
sense of constructive set theory, that is,

$$α̃(x) = α̃(x') → β̃(f(x)) = β̃(f(x')).$$

Define the equivalence relations

$$(x =_{ᾱ} x') = (α̃(x) = α̃(x'))$$

and

$$(y =_{β̄} y') = (β̃(y) = β̃(y'))$$

on $ᾱ$ and $β̄$, respectively.  By the extensional axiom of choice in type
theory, the choice function $f : ᾱ → β̄$ can be taken to be extensional with
respect to these two equivalence relations,

$$x =_{ᾱ} x' → f(x) =_{β̄} f(x'),$$

which ensures that $φ$, defined as above, is a function from $α$ to $β$ in the
sense of constructive set theory.

**Corollary.**  *When constructive type theory (including one universe and the
$W$-operation) is strengthened by the extensional axiom of choice, it interprets
all of ZFC.*

*Proof.*  We already know from Aczel that $\text{ZF}$ is equivalent to
$\text{CZF} + \text{EM}$.[^18]  Hence $\text{ZFC}$ is equivalent to
$\text{CZF} + \text{EM} + \text{AC}$.  But, by Diaconescu’s theorem as
transferred to constructive set theory by Goodman and Myhill, the law of
excluded middle follows from the axiom of choice in the context of constructive
set theory.[^19]  It thus suffices to interpret $\text{CZF} + \text{AC}$ in
$\text{CTT} + \text{ExtAC}$, and this is precisely what the Aczel interpretation
does, by the previous theorem.

Another way of reaching the same conclusion is to interchange the order of the
last two steps in the proof just given, arguing instead that
$\text{ZFC} = \text{CZF} + \text{EM} + \text{AC}$ is interpretable in
$\text{CTT} + \text{EM} + \text{ExtAC}$ by the previous theorem, and then
appealing to the type-theoretic version of Diaconescu’s theorem, according to
which the law of excluded middle follows from the extensional axiom of choice in
the context of constructive type theory.[^20]  The final conclusion is anyhow
that $\text{ZFC}$ is interpretable in $\text{CTT} + \text{ExtAC}$.

--------------------------------------------------------------------------------

When Zermelo’s axiom of choice is formulated in the context of constructive type
theory instead of Zermelo-Fraenkel set theory, it appears as $\text{ExtAC}$, the
extensional axiom of choice

$$(∀i : I)(∃x : S)A(i, x) → (∃f : I → S)(\text{Ext}(f) ∧ (∀i : I)A(i,f(i))),$$

where

$$\text{Ext}(f) = (∀i,j : I)(i =_I j → f(i) =_S f(j)),$$

and it then becomes manifest what is the problem with it: it breaks the
principle that you cannot get something from nothing.  Even if the relation
$A(i, x)$ is extensional with respect to its two arguments, the truth of the
antecedent $(∀i : I)(∃x : S)A(i, x)$, which does guarantee the existence of a
choice function $f : I → S$ satisfying $(∀i : I)A(i, f(i))$, is not enough to
guarantee the extensionality of the choice function, that is, the truth of
$\text{Ext}(f)$.  Thus the problem with Zermelo’s axiom of choice is not the
existence of the choice function but its extensionality, and this is not visible
within an extensional framework, like Zermelo-Fraenkel set theory, where all
functions are by definition extensional.

If we want to ensure the extensionality of the choice function, the antecedent
clause of the extensional axiom of choice has to be strengthened.  The natural
way of doing this is to replace $\text{ExtAC}$ by $\text{AC!}$, the axiom of
unique choice, or no choice,

$$(∀i : I)(∃!x : S)A(i, x) → (∃f : I → S)(\text{Ext}(f) ∧ (∀i : I)A(i, f(i))),$$

which is as valid as the intensional axiom of choice.  Indeed, assume
$(∀i : I)(∃!x : S)A(i, x)$ to be true.  Then, by the intensional axiom of
choice, there exists a choice function $f : I → S$ satisfying
$(∀i : I)A(i, f(i))$.  Because of the uniqueness condition, such a function
$f : I → S$ is necessarily extensional.  For suppose that $i, j : I$ are such
that $i =_I j$ is true.  Then $A(i, f(i))$ and $A(j, f(j))$ are both true.
Hence, by the extensionality of $A(i, x)$ in its first argument, so is
$A(i, f(j))$.  The uniqueness condition now guarantees that $f(i) =_S f(j)$,
that is, that $f : I → S$ is extensional.  The axiom of unique choice
$\text{AC!}$ may be considered as the valid form of extensional choice, as
opposed to $\text{ExtAC}$, which lacks justification.

--------------------------------------------------------------------------------
```
-- TODO
```
--------------------------------------------------------------------------------

The inability to distinguish between the intensional and the extensional axiom
of choice has led to one’s taking the need for the axiom of choice in proving
that the union of a countable sequence of countable sets is again countable,
that the real numbers, defined as Cauchy sequences of rational numbers, are
Cauchy complete, etc., as a justification of Zermelo’s axiom of choice.  As
Zermelo himself wrote towards the end of the short paper in which he originally
introduced the axiom of choice,

<blockquote>
Dieses logische Prinzip läßt sich zwar nicht auf ein noch einfacheres
zurückführen, wird aber in der mathematischen Deduktion überall unbedenklich
angewendet.[^21]
</blockquote>

What Zermelo wrote here about the omnipresent, and often subconscious, use of
the axiom of choice in mathematical proofs is incontrovertible, but it concerns
the constructive, or intensional, version of it, which follows almost
immediately from the strong rule of existential elimination.  It cannot be taken
as a justification of his own version of the axiom of choice, including as it
does the extensionality of the choice function.

Within an extensional foundational framework, like topos theory or constructive
set theory, it is not wholly impossible to formulate a counterpart of the
constructive axiom of choice, despite of its intensional character, but it
becomes complicated.  In topos theory, there is the axiom that there are enough
projectives, which is to say that every object is the surjective image of a
projective object, and, in constructive set theory, Aczel has introduced the
analogous axiom that every set has a base.[^22]  Roughly speaking, this is to
say that every set is the surjective image of a set for which the axiom of
choice holds.  The technical complication of these axioms speaks to my mind for
an intensional foundational framework, like constructive type theory, in which
the intuitive argument why the axiom of choice holds on the
Brouwer-Heyting-Kolmogorov interpretation is readily formalized, and in which
whatever extensional notions that are needed can be built up, in agreement with
the title of Martin Hofmann’s thesis, Extensional Constructs in Intensional Type
Theory.[^23]  Extensionality does not come for free.

Finally, since this is only a couple of weeks from the centenary of Zermelo’s
first formulation of the axiom of choice, it may not be out of place to remember
the crucial role it has played for the formalization of both Zermelo-Fraenkel
set theory and constructive type theory.  In the case of set theory, there was
the need for Zermelo of putting his proof of the well-ordering theorem on a
formally rigorous basis, whereas, in the case of type theory, there was the
intuitively convincing argument which made axiom of choice evident on the
constructive interpretation of the logical operations, an argument which
nevertheless could not be faithfully formalized in any then existing formal
system.

<!-- ----------------------------------------------------------------------- -->

[^1]:  G. Cantor, Über unendliche lineare Punktmannigfaltigkeiten. Nr. 5, *Math.
       Annalen,* Vol. 21, 1883, pp. 545–591. Reprinted in *Gesammelte
       Abhandlungen,* Edited by E. Zermelo, Springer-Verlag, Berlin, 1932,
       pp. 165–208.

[^2]:  G. H. Moore, *Zermelo’s Axiom of Choice: Its Origins, Development, and
       Influence,* Springer-Verlag, New York, 1982, p. 51.

[^3]:  E. Zermelo, Beweis, daß jede Menge wohlgeordnet werden kann. (Aus einem
       an Herrn Hilbert gerichteten Briefe.), *Math. Annalen,* Vol. 59,
       pp. 514–516.

[^4]:  E. Zermelo, Neuer Beweis für die Möglichkeit einer Wohlordnung, *Math.
       Annalen,* Vol. 65, 1908, pp. 107–128.

[^5]:  E. Zermelo, Untersuchungen über die Grundlagen der Mengenlehre. I, *Math.
       Annalen,* Vol. 65, 1908, pp. 261–281.

[^6]:  G. H. Moore, op. cit., pp. 92–137.

[^7]:  M. Zorn, A remark on method in transfinite algebra, *Bull. Amer. Math.
       Soc.,* Vol. 41, 1935, pp. 667–670.

[^8]:  R. Baire, É. Borel, J. Hadamard and H. Lebesgue, Cinq lettres sur la
       théorie des ensembles, *Bull. Soc. Math. France,* Vol. 33, 1905,
       pp. 261–273.

[^9]:  É. Borel, Quelques remarques sur les principes de la théorie des
       ensembles, *Math. Annalen,* Vol. 60, 1905, pp. 194–195.

[^10]: L. E. J. Brouwer, *Over de grondslagen der wiskunde,* Maas \& van
       Suchtelen, Amsterdam, 1907. English translation in *Collected Works,*
       Vol. 1, Edited by A. Heyting, North–Holland, Amsterdam, 1975, pp. 11–101.

[^11]: E. Bishop, *Foundations of Constructive Analysis,* McGraw-Hill, New York,
       1967, p. 9.

[^12]: R. Diaconescu, Axiom of choice and complementation, *Proc. Amer. Math.
       Soc.,* Vol. 51, 1975, pp. 176–178.

[^13]: E. Zermelo, op. cit., footnote 3, p. 514.

[^14]: E. Zermelo, op. cit., footnote 4, p. 110.

[^15]: A. N. Whitehead, On cardinal numbers, *Amer. J. Math.,* Vol. 24, 1902,
       pp. 367–394.

[^16]: B. Russell, On some difficulties in the theory of transfinite numbers and
       order types, *Proc. London Math. Soc.,* Ser. 2, Vol. 4, 1906, pp. 29–53.

[^17]: P. Aczel, The type theoretic interpretation of constructive set theory,
       *Logic Colloquium ’77,* Edited by A. Macintyre, L. Pacholski and
       J. Paris, North-Holland, Amsterdam, 1978, pp. 55–66.

[^18]: P. Aczel, op. cit., p. 59.

[^19]: N. D. Goodman and J. Myhill, Choice implies excluded middle, *Zeitschrift
       für mathematische Logik und Grundlagen der Mathematik,* Vol. 24, 1978,
       p. 461.

[^20]: S. Lacas and B. Werner, Which choices imply the Excluded Middle? About
       Diaconescu’s trick in Type Theory, Unpublished, 1999, pp. 9–10.  I am
       indebted to Jesper Carlström for providing me with this reference.

[^21]: E. Zermelo, op. cit., footnote 3, p. 516.

[^22]: P. Aczel, The type theoretic interpretation of constructive set theory:
       choice principles, *The L. E. J. Brouwer Centenary Symposium,* Edited by
       A. S. Troelstra and D. van Dalen, North-Holland, Amsterdam, 1982,
       pp. 1–40.

[^23]: M. Hofmann, *Extensional Constructs in Intensional Type Theory,*
       Springer-Verlag, London, 1997.
