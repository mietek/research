---
author:  Aczel
hauthor: Peter Aczel
year:    1978
title:   The type theoretic interpretation of constructive set theory
lang:    en
card:    'P. Aczel, [The type theoretic interpretation of constructive set theory (***mi***)
         ](), [(orig.)](https://sci-hub.st/10.1016/S0049-237X(08)71989-X), *Logic Colloquium ’77*,
         Edited by A. Macintyre, L. Pacholski, and J. Paris, North Holland, Amsterdam, 1978,
         pp. 55–66.'
---

```
-- Mechanised by Miëtek Bak

module mi.Aczel1978 where

-- TODO
```

> By adding to Martin-Löf’s intuitionistic theory of types a ‘type of sets’ we give a constructive
> interpretation of constructive set theory.  This interpretation is a constructive version of the
> classical conception of the cumulative hierarchy of sets.[^1]


## Introduction

Intuitionistic mathematics can be structured into two levels.  The first level arises directly out
of Brouwer’s criticism of certain methods and notions of classical mathematics.  In particular the
notion of ‘truth’ that gives rise to the law of excluded middle was rejected and instead the meaning
of mathematical statements was to be based on the notion of ‘proof’.  While implicit in this first
level of intuitionism was a theory of meaning quite different from the classical one, it was
nevertheless the case that the body of mathematics that could be developed within this level
remained a part of classical mathematics.  Because Brouwer felt that mathematical analysis could not
be developed adequately on this basis he was led to formulate his own conception of the continuum.
This conception involved the mathematical treatment of incompletely specified objects such as free
choice sequences.  The second level of intuitionism builds on the first level but also includes
these radical ideas that turn out to be incompatible with classical mathematics.  Although
considerable effort has been made over the years to make these ideas more transparent they have
remained rather obscure to most mathematicians and the mathematics based on them has had a very
limited following.

Since Bishop’s book [[3]](#r3){#rr3 .rr} appeared, it has become clear that, in spite of Brouwer’s
views, constructive analysis can be developed perfectly adequately while staying within the first
level of intuitionism.  This fact has led to a renewed interest in this part of intuitionism.  The
desire has been to find an analogue, for Bishop’s constructive mathematics, of the generally
accepted formal system $\text{ZF}$ for classical mathematics.  Several approaches have been tried
and there has been some controversy over their relative merits.  Two such approaches are
‘Constructive Set Theory’ (see [[7]](#r7){#rr7 .rr} and [[13]](#r13){#rr13 .rr}) and ‘Intuitionistic
Type Theory’ (see [[11]](#r11){#rr11 .rr}).  In this paper we take the view that these, and perhaps
other approaches, are not necessarily in conflict with each other.  Constructive set theory
suppresses all explicit constructive notions in order to be as familiar as possible to the classical
mathematician.  On the other hand type theory aims to give a rigorous foundation for the primitive
notions of constructive mathematics.

The appeal of Bishop’s book is that it wastes little time on the analysis of constructive concepts
but instead develops analysis in a language mostly familiar to the classical mathematician.  In
constructive set theory this is taken a stage further.  As in $\text{ZF}$ there are just the notions
of set and set membership with an axiom system that is a subsystem of $\text{ZF}$ using
intuitionistic logic, and including the axiom of extensionality.  In such a system the direct
constructive content of Bishop’s notions has been lost and there arises the crucial question:  What
is the constructive meaning of the notion of set used in constructive set theory?  We aim to answer
that question in this paper.  What is needed is a rigorous framework in which the primitive notions
of constructive mathematics are directly displayed, together with a natural interpretation of
constructive set theory in that framework.  We shall give such a framework based on the
intuitionistic type theory of [[11]](#r11){#rr11-1 .rr}.  We could have taken instead a system of
‘Explicit Mathematics’ (see [[5]](#r5){#rr5 .rr} and [[2]](#r2){#rr2 .rr}).  But systems of explicit
mathematics leave the logical notions unanalysed, whereas type theory is a logic free theory of
constructions within which the logical notions can be defined.  For this reason we consider type
theory to be more fundamental.

The axiom system $\text{CZF}$ (Constructive $\text{ZF}$) is set out in §1 and some elementary
properties are given in §2.  The system is closely related to the systems considered by Myhill and
Friedman in their papers.  In §3 we summarise the type theoretic notions of [[11]](#r11){#rr11-2
.rr} and introduce the type of sets.  The interpretation of $\text{CZF}$ is set up in §4 and its
correctness is proved in §5 and §6.  Finally in §7 we consider a new principle of choice for
constructive set theory.

Formally, the type of sets was first introduced by Leversha in [[10]](#r10){#rr10 .rr} where it was
used to give a complicated type theoretic interpretation of Myhill’s original formulation of
constructive set theory in [[13]](#r13){#rr13-1 .rr}.  Unfortunately it was not realised at that
time that the type itself gave a constructive notion of set.  Instead it was only used as an
appropriate constructive notion of ordinal to use in indexing the stages of Leversha’s construction.


## 1. The axiom system $\text{CZF}$

We formulate $\text{CZF}$ in a first order language $\mathcal{L}$ having the logical primitives
$\bot$, $∨$, $∧$, $→$, $∀x$, $∃x$, the restricted quantifiers $(∀x∈y)$, $(∃x∈y)$ and the binary
relation symbols $∈$ and $=$.  We assume a standard axiomatisation of intuitionistic logic.  The
remaining axioms of $\text{CZF}$ are divided into two groups.

### Structural axioms

Defining schemes for the restricted quantifiers.

$$(∀x∈y)φ(x) ↔ ∀x(x∈y → φ(x))$$

$$(∃x∈y)φ(x) ↔ ∃x(x∈y ∧ φ(x))$$

Equality axioms.

$$x = y ↔ ∀z(z∈x ↔ z∈y)$$

$$x = y ∧ y∈z ↔ x∈z$$

Set induction scheme.

$$∀y ((∀x∈y)φ(x) → φ(y)) → ∀xφ(x)$$

### Set existence axioms

Pairing.

$$∃z(x∈z ∧ y∈z)$$

Union.

$$∃z(∀y∈x)(∀u∈y)(u∈z)$$

Restricted separation.

```
-- TODO
```

## References

::: {.references}

1.   ::: {#r1}
     P. Aczel, [The strength of Martin-Löf’s intuitionistic type theory with one universe
     ](https://jyu.finna.fi/Record/vaari.1584852),
     *Proc. Symp. Math. Logic, Oulu ’74 and Helsinki ’75*, Edited by S. Miettinen and J. Väänänen,
     University of Helsinki, 1977, pp. 1–32.
     <!-- TODO: document missing -->
     [↩](#rr1){.rb}
     :::

2.   ::: {#r2}
     M. Beeson, [Principles of continuous choice and continuity of functions in formal systems
     for constructive mathematics](https://sci-hub.st/10.1016/S0003-4843(77)80003-X), *Annals
     Math. Logic*, Vol. 12(3), 1977, pp. 249–322.
     [↩](#rr2){.rb}
     :::

3.   ::: {#r3}
     E. Bishop, *[Foundations of Constructive Analysis
     ](https://library.lol/main/D69762DE514CE40FAA389C6F178F66D4)*, McGraw-Hill, New York, 1967.
     <!-- TODO: DOI missing -->
     [↩](#rr3){.rb}
     :::

4.   ::: {#r4}
     A. Blass, [Injectivity, projectivity, and the axiom of choice
     ](https://sci-hub.st/10.1090/S0002-9947-1979-0542870-6), *Trans. Amer. Math. Soc.*, Vol. 255,
     1979, pp. 31–59.
     [↩](#rr4){.rb}
     :::

5.   ::: {#r5}
     S. Feferman, [A language and axioms for explicit mathematics
     ](https://sci-hub.st/10.1007/BFb0062852), *Algebra and Logic*, *Lec. Notes Math.*, Vol. 450,
     Edited by J. N. Crossley, Springer-Verlag, Berlin, 1975, pp. 87–139.
     [↩](#rr5){.rb}
     :::

6.   ::: {#r6}
     H. Friedman, [The consistency of set theory relative to a theory with intuitionistic logic
     ](https://sci-hub.st/10.2307/2272068), *J. Symb. Logic*, Vol. 38(2), 1973, pp. 315–319.
     [↩](#rr6){.rb}
     :::

7.   ::: {#r7}
     H. Friedman, [Set theoretic foundations for constructive analysis
     ](https://sci-hub.st/10.2307/1971023), *Annals of Math.*, Vol. 105(1), 1977, pp. 1–28.
     [↩](#rr7){.rb}
     :::

8.   ::: {#r8}
     R. Grayson, ~~A sheaf approach to models of set theory~~, M. Sc. thesis, University of
     Oxford, 1975.
     <!-- TODO: document missing -->
     [↩](#rr8){.rb}
     :::

9.   ::: {#r9}
     H. R. Jervell, [Constructive Universes I](https://sci-hub.st/10.1007/BFb0103103), *Higher Set
     Theory*, *Lec. Notes Math.*, Vol. 669, Edited by G. H. Müller and D. S. Scott, Springer-Verlag,
     Berlin, 1978, pp. 73–98.
     [↩](#rr9){.rb}
     :::

10.  ::: {#r10}
     G. Leversha, [Formal systems for constructive mathematics
     ](https://solo.bodleian.ox.ac.uk/permalink/44OXF_INST/ao2p7t/cdi_proquest_journals_301376483),
     Ph. D. thesis, University of Manchester, 1976.
     <!-- TODO: document missing -->
     [↩](#rr10){.rb}
     :::

11.  ::: {#r11}
     P. Martin-Löf, [An intuitionistic theory of types: Predicative part
     ](https://sci-hub.st/10.1016/S0049-237X(08)71945-1), *Logic Colloquium ’73*, *Stud. Logic
     Found. Math.*, Vol. 80, Edited by H. E. Rose and J. C. Shepherdson, North Holland, Amsterdam,
     1975, pp. 73–118.
     [↩](#rr11){.rb}
     [↩](#rr11-1){.rb}
     [↩](#rr11-2){.rb}
     :::

12.  ::: {#r12}
     J. Mayberry, [On the consistency problem for set theory: An essay on the Cantorian foundations
     of mathematics (part I)](https://sci-hub.st/10.1093/bjps/28.1.1), [(part II)
     ](https://sci-hub.st/10.1093/bjps/28.2.137), *Brit. J. Phil. Sci.*, Vol. 28(1–2), 1977,
     pp. 1–34 (part I), pp. 137–170 (part II).
     [↩](#rr12){.rb}
     :::

13.  ::: {#r13}
     J. Myhill, [Constructive set theory](https://sci-hub.st/10.2307/2272159), *J. Symb. Logic,*
     Vol. 40(3), 1975, pp. 347–382.
     [↩](#rr13){.rb}
     [↩](#rr13-1){.rb}
     :::

14.  ::: {#r14}
     L. Pozsgay, [Liberal intuitionism as a basis for set theory
     ](https://library.lol/main/5F885CC6CC2FA1B1EB7BC55FC69098F1), *Axiomatic Set Theory, Part 1*,
     *Proc. Symp. Pure Math.*, Vol. 13, Edited by D. S. Scott, University of California, Los
     Angeles, 1971, pp. 321–330.
     [↩](#rr14){.rb}
     :::

:::

<!-- ******************************************************************************************* -->

[^1]:  The ideas for this paper were germinating during a visit to Caltech, supported by NSF grant
       MPS 75-07562, and came to fruition while visiting Utrecht University.  The results were
       first announced in an abstract for the 1976 Oxford Logic Colloquium.
       <!-- -->
