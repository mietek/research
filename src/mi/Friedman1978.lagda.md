---
author:  H. Friedman
hauthor: Harvey Friedman[^1]
year:    1978
title:   Classically and intuitionistically provably recursive functions
lang:    en
wip:     yes
card:
  - H. Friedman (1978)
  - '[Classically and intuitionistically provably recursive functions
    ](https://sci-hub.st/10.1007/BFb0103100)'
  - '*Higher Set Theory, Lecture Notes Math.*, Vol. 669, Edited by G. H. Müller and D. S. Scott,
    Springer, Berlin, pp. 345–350.'
todo:
  - '${e}(n)$ is applying the $e$th partial (primitive?) recursive function to $n$'

---

```
-- Not yet mechanised by Miëtek Bak
-- TODO: rest of text

module mi.Friedman1978 where
```

Among the most interesting metamathematical results connected with constructivity is that Peano
arithmetic (PA) is a conservative extension of Heyting arithmetic (HA), (which is PA with
intuitionistic logic), for $Π^0_2$ sentences.  In other words, every Turing machine program that,
provably in PA, converges at all arguments, also does provably in HA.

The proof consists of two parts.  Firstly, the double negation translation of Gödel is used to
interpret PA within HA.  In particular, if a formula $(∃n)(F(n,m) = 0)$ is provable in PA, then
$\neg\neg (∃n)(F(n,m) = 0)$ is provable in HA.  Here $F$ represents an arbitrary primitive
recursive function.

The final part consists in showing that HA is closed under Markov’s rule.  In this case, we need to
show if $\text{HA} ⊢ \neg\neg (∃n)(F(n,m) = 0)$ then $\text{HA} ⊢ (∃n)(F(n,m) = 0).$  This
part of the proof is technically far more difficult than the first, which is a direct translation
that can be routinely verified.  Two principal methods for the second part are

(i)   a proof-theoretic analysis of HA, and
(ii)  the Gödel functional interpretation of HA.

Either a delicate proof-theoretic analysis of HA which is sensitive to the axioms and rules of
inference used to represent HA, or a semantic analysis of HA which is obviously sensitive to the
meaning of the axioms of HA, was needed.  The double negation translation depends only on the
syntactic nature of the axioms in HA as presented in a standard Hilbert style predicate logic.

We give a new proof of the closure of HA under Markov’s rule which is an elementary syntactic
argument in the same sense that the double negation translation is.  The proof establishes closure
for many systems.  In particular, for intuitionistic systems of higher order arithmetic and type
theory, for which earlier analyses (comparatively quite complicated and delicate) of Spector
(functional interpretation), Girard (functional interpretation), Prawitz (normalization), and others
were used.  Since the double negation translation goes through straightforwardly for such systems,
we again have the conservative extension of the classical systems over the intuitionistic systems
for $Π^0_2$ sentences.

We also apply the method to a formulation of intuitionistic Zermelo-Fraenkel set theory.  We show
that classical ZF and intuitionistic ZF have the same provably recursive functions.  We also show
that they have the same provable ordinals, in an appropriate sense.  No adequate functional
interpretation or proof-theoretic analysis are presently known for such systems.


## 1.  The translations in many-sorted predicate logic

The double negation translation $φ^-$ of a formula $φ$ of intuitionistic many-sorted predicate logic
without identity is defined by

$$
\begin{aligned}
  φ^-        &= \neg\negφ \text{ for atomic } φ; \\
  (\neg φ)^- &= \neg (φ^-); \\
  (φ ∧ ψ)^-  &= φ^- ∧ ψ^-; \\
  (φ ∨ ψ)^-  &= \neg\neg (φ^- ∨ ψ^-); \\
  (∀x)(φ)^-  &= (∀x)(φ^-); \\
  (∃x)(φ)^-  &= \neg\neg (∃x)(φ^-); \\
  (φ → ψ)^- &= φ^- → ψ^-.
\end{aligned}
$$

Let $⊢_I$ refer to provability in the intuitionistic logic, and $⊢_C$ to provability in the
classical logic.  The basic facts about the double negation translation are as follows.


#### Theorem 1.1.

If $φ ⊢_C ψ$ then $φ^- ⊢_I ψ^-.$  Also $⊢_I (\neg\neg (φ^-)) → φ^-$, and $⊢_I (φ^-)^- ↔ φ^-.$

##### Proof.

::: {.qed}
These are well known.  The first is proved by induction on the length of proofs in a standard
Hilbert style axiomatization.  The rest is proved by induction on the formula $φ.$
:::

We now give our translation.  Fix $A$ to be any formula.  Write every formula with $∀,$ $∃,$ $∧,$
$∨,$ $→,$ $\bot.$  Let $φ$ be any formula none of whose bound variables is free in $A.$

Define the $A$-translation $φ_A$ of $φ$ to be the result of simultaneously replacing each atomic
subformula $ψ$ of $φ$ by $(ψ ∨ A)$.


#### Theorem 1.2.

If $φ ⊢_I ψ$ and $φ_A,$ $ψ_A$ are defined, then $φ_A ⊢_I ψ_A.$  Also $A ⊢_I φ_A.$

##### Proof.

::: {.qed}
This is also straightforwardly proved by induction on the length of proofs.
:::


## 2.  First order arithmetic

Let HA be Heyting arithmetic formulated with primitive recursive function symbols in one-sorted
predicate logic.  Let PA be Peano arithmetic, which is the same as HA except classical logic is
used.


#### Lemma 1.

The double negation translation of every axiom of HA is provable in HA.  Hence if $\text{PA} ⊢ φ$
then $\text{HA} ⊢ φ^-.$

##### Proof.

::: {.qed}
This is well known and straightforward.
:::

Markov’s rule (for primitive recursive matrix) states that if $\neg\neg (∃n)(F(n,m) = 0)$ is
provable, then so is $(∃n)(F(n,m) = 0).$  We must show that HA is closed under Markov’s rule.


#### Lemma 2.

For every $A$, the $A$-translation of every axiom of HA, none of whose bound variables are free in
$A$, is provable in HA.  Hence if $\text{HA} ⊢ φ$ then $\text{HA} ⊢ φ_A$.

##### Proof.

::: {.qed}
This is a straightforward verification.
:::


#### Lemma 3.

If $\text{HA} ⊢ \neg\neg (∃n)(F(n,m) = 0),$ then $\text{HA} ⊢ (∃n)(F(n,m) = 0).$

##### Proof.

::: {.qed}
We have $\text{HA} ⊢ ((∃n)(F(n,m) = 0) → \bot) → \bot.$  By lemma 2, using
$A = (∃n)(F(n,m) = 0),$ we have
$\text{HA} ⊢ ((∃n)(F(n,m) = 0 ∨ (∃n)(F(n,m) = 0)) → (∃n)(F(n,m) = 0)) → (∃n)(F(n,m) = 0)).$
Hence $\text{HA} ⊢ (∃n)(F(n,m) = 0).$
:::


#### Theorem 2.1.

If $\text{PA} ⊢ (∀n)(∃m)(F(n,m) = 0)$ then $\text{HA} ⊢ (∀n)(∃m)(F(n,m) = 0).$

##### Proof.

::: {.qed}
By lemma 1, $\text{HA} ⊢ \neg\neg (∃m)(F(n,m) = 0).$  By lemma 3,
$\text{HA} ⊢ (∃m)(F(n,m) = 0.$
:::

Sometimes the full Markov rules is considered: If $(∀n)(∀m)(φ(n,m) ∨ \neg φ(n,m))$ and
$\neg\neg (∃m)(φ(n,m))$ are provable, then $(∃m)(φ(n,m))$ is provable.  We can obtain the full
Markov rule using the following lemmas.


#### Lemma 4.

HA is closed under Church’s rule.  I.e., if $\text{HA} ⊢ (∀n)(∃m)(φ(n,m)),$ then there is an $e$
such that $\text{HA} ⊢ (∀n)(φ(n,\{e\}(n))).$

##### Proof.

::: {.qed}
This is well known.
:::


#### Lemma 5.

If $\text{HA} ⊢ φ(n,m) ∨ \neg φ(n,m),$ then there is an $F$ such that
$\text{HA} ⊢ φ(n,m) ↔ (∃r)(F(r,n,m) = 0).$

##### Proof.

::: {.qed}
Immediate from lemma 4.
:::


#### Theorem 2.2.

HA is closed under the full Markov rule.  Also, suppose $\text{HA}⊢ φ(n,m) ∨ \neg φ(n,m),$ and
$\text{PA} ⊢ (∀n)(∃m)(φ(n,m)).$  Then $\text{HA} ⊢ (∀n)(∃m)(φ(n,m)).$

##### Proof.

::: {.qed}
Immediate from lemmas 3, 5, and theorem 2.1.
:::


## 3.  The theory of finite types

For each $n ≥ 1$ we have variables $n^n_m$ over sets of type $n$ over natural numbers.  We also have
variables $n_i$ over natural numbers.  Of the many essentially equivalent formulations, we use $=$
only among natural numbers, the number constant $0$, symbols for all primitive recursive functions,
and $∈$ between terms of type $n$ and type $n+1$ only (natural numbers are of type 0).  For
completeness, the axioms of $T$ are:

1.  $\neg S(n) = 0;$
    $S(n) = S(m) → n = m;$
    $n = m;$
    $n = m → m = n;$
    $(n = m ∧ m = r) → n = r;$
    $(n_1 = m_1 ∧ … ∧ n_k = m_k) → F(n_1, …, n_k) = F(m_1, …, m_k);$
    $n = m → (n ∈ x^1 ↔ m ∈ x^1).$

2.  Primitive recursive defining equations.

3.  $(φ[n/0] ∧ (∀n)(φ → φ[n/S(n)])) → φ,$ where $φ$ is arbitrary.

4.  $(∃x^1)(∀n)(n ∈ x^1 ↔ φ),$ where $x^1$ is not free in $φ$, and
    $(∃x^{n+1})(∀y^n)(y^n ∈ x^{n+1} ↔ ψ),$ where $x^{n+1}$ is not free in $ψ.$

```
-- TODO
```


## References

::: {.references}

1.  ::: {#r1}
    H. Friedman (1973) [The consistency of classical set theory relative to a set theory with
    intuitionistic logic](https://sci-hub.st/10.2307/2272068),
    *J. Symbolic Logic*, Vol. 38(2), pp. 315–319. [↩](#rr6){.rb}
    :::

:::

[^1]:  This research was partially supported by NSF grant MCS 77-01638.  The results were obtained
       in February, 1977.
