---
author:  C. McBride
hauthor: Conor McBride
year:    2006
title:   Type-preserving renaming and substitution
htitle:  Type-preserving<br>renaming and substitution
lang:    en
card:
  - C. McBride (2006)
  - '[Type-preserving renaming and substitution
    ](http://strictlypositive.org/ren-sub.pdf)'
  - Manuscript.
todo:
  - DOI missing
---


```
-- Re-mechanised by Miëtek Bak

module mi.McBride2006 where

id : ∀ {𝒶} {A : Set 𝒶} → A → A
id x = x
```

I present a substitution algorithm for the simply-typed λ-calculus, represented in the style of
Altenkirch and Reus [(1999)](#r1){#rr1 .rr} which is statically guaranteed to respect scope and
type.  Moreover, I use a single traversal function, instantiated first to renaming, then to
substitution.  The program is written in Epigram [(McBride & McKinna, 2004)](#r5){#rr5 .rr}.


## 1. Introduction

In this paper, I give a small but indicative example of programming with *inductive families of
datatypes* [(Dybjer, 1991)](#r4){#rr4 .rr} in the dependently typed functional programming language,
Epigram [(McBride & McKinna, 2004)](#r5){#rr5-1 .rr}.  I present *type-preserving* renaming and
substitution for the *type-correct* representation of the simply-typed $λ$-calculus given by
Altenkirch and Reus [(1999)](#r1){#rr1-1 .rr}.  I should draw attention to two aspects of this
program:

-  Renaming and substitution turn out to be instances of a single traversal operation, pushing
   functions from variables to ‘stuff’ through terms, for a suitable notion of ‘stuff’.  This
   traversal operation is structurally recursive, hence clearly total.

-  Type preservation is clearly promised by the types of these programs; in their bodies, the amount
   of syntax required to fulfil this promise is *none whatsoever*.  The ill-concealed ulterior
   motive of this paper is to put Epigram’s notational innovations through their paces.

The only significant cosmetic treatment I have given the code is to delete a few brackets and make
some of the operators infix: the honest ASCII thus looks a little clumsier.  I suppressed no
details: the process usually referred to vaguely as ‘type inference’ is hard at work here, inferring
*values* determined by the dependent types in which they occur.


## 2. Simply typed $λ$-calculus

Figure 1 gives the now traditional definition of the type-correct simply-typed $λ$-terms in
Epigram’s two-dimensional syntax.  The natural deduction style emphasises the connection between
inductive families of datatypes and deduction systems.  Each rule types the general usage of a new
symbol, below the line, in terms of parameters typed above the line.  You can read ‘$:$’ as ‘has
type’ and ‘$\star$’ as the type of types.

::: {.align-top}
$$
\begin{aligned}
  &\underline{\textrm{data}}
    &&\frac{}{\textsf{Ty} : \star}
    &&\underline{\textrm{where}}
    &&\frac{}{\bullet : \textsf{Ty}}\quad
    \frac{S,T : \textsf{Ty}}{S \vartriangleright T : \textsf{Ty}}\\\\
  &\underline{\textrm{data}}
    &&\frac{}{\textsf{Ctxt} : \star}
    &&\underline{\textrm{where}}
    &&\frac{}{\mathcal{E} : \textsf{Ctxt}}\quad
    \frac{Γ : \textsf{Ctxt}\quad S : \textsf{Ty}}{Γ :: S : \textsf{Ctxt}}\\\\
  &\underline{\textrm{data}}
    &&\frac{Γ : \textsf{Ctxt}\quad T : \textsf{Ty}}{Γ ∋ T : \star}
    &&\underline{\textrm{where}}
    &&\frac{}{\textsf{vz} : Γ :: S ∋ S}\quad
    \frac{x : Γ ∋ T}{\textsf{vs}\ x : Γ :: S ∋ T}\\\\
  &\underline{\textrm{data}}
    &&\frac{Γ : \textsf{Ctxt}\quad T : \textsf{Ty}}{Γ \blacktriangleright T : \star}
    &&\underline{\textrm{where}}
    &&\frac{x : Γ ∋ T}{\textsf{var}\ x : Γ \blacktriangleright T}\quad
    \frac{t : Γ :: S \blacktriangleright T}
         {\textsf{lam}\ t : Γ \blacktriangleright S \vartriangleright T}\\[11pt]
    &&&&&&&\frac{f : Γ \blacktriangleright S \vartriangleright T\quad s : Γ \blacktriangleright S}
                {\textsf{app}\ s\ t : Γ \blacktriangleright T}
\end{aligned}
$$

Fig. 1.  The simply typed λ-calculus

```
data Ty : Set where
  •   : Ty
  _▷_ : ∀ (S T : Ty) → Ty

data Ctxt : Set where
  ℰ   : Ctxt
  _∷_ : ∀ (Γ : Ctxt) → (S : Ty) → Ctxt

data _∋_ : Ctxt → Ty → Set where
  vz  : ∀ {Γ S} → (Γ ∷ S) ∋ S
  vs  : ∀ {Γ S T} (x : Γ ∋ T) → (Γ ∷ S) ∋ T

data _▶︎_ (Γ : Ctxt) : Ty → Set where
  var : ∀ {T} (x : Γ ∋ T) → Γ ▶︎ T
  lam : ∀ {S T} (t : (Γ ∷ S) ▶︎ T) → Γ ▶︎ (S ▷ T)
  app : ∀ {S T} (f : Γ ▶︎ (S ▷ T)) (s : Γ ▶︎ S) → Γ ▶︎ T
```
:::

This may seem like overkill for ‘simple’ definitions like $\textsf{Ty}$ (for simple types) and
$\textsf{Ctxt}$ (for contexts—reversed lists of simple types), which you might imagine writing
grammar-style, like this:

$$
\begin{aligned}
  &\underline{\textrm{data}}\ \textsf{Ty} =
    \bullet\ |\ \textsf{Ty} \vartriangleright \textsf{Ty}\\
  &\underline{\textrm{data}}\ \textsf{Ctx} =
    \mathcal{E}\ |\ \textsf{Ctxt} :: \textsf{Ty}
\end{aligned}
$$

The production $\textsf{Ty} \vartriangleright \textsf{Ty}$ makes perfect sense in a language where
types and values are rigidly separated, but in Epigram it’s actually a well-formed but ill-typed
application!  Our notation invites the programmer to write a set of *patterns* for data, naming
their parts: these patterns and these names reappear when you edit interactively, as the machine
generates exhaustive case analyses on the left-hand sides of programs.

Naming becomes practically indispensable once types start to depend on values.  Moreover, *inductive
families of datatypes* assign individual return types for each constructor, an unconventional
practice which again leads us away from the conventional notation.

Here, the ‘$\ni$’ family presents *variables* as an inference system for context membership.  This
representation amounts to de Bruijn indices [(de Bruijn, 1972)](#r3){#rr3 .rr}, but correctly typed
and scoped. Meanwhile, the ‘$\blacktriangleright$’ family presents simply-typed terms via their
typing rules, extending the context under a $\textsf{lam}$ and policing the compatibility of domain
and argument in an $\textsf{app}.$  Note that ‘$::$’ and ‘$\vartriangleright$’ bind more tightly
than ‘$\ni$’ and ‘$\blacktriangleright$’.

The form of a rule’s conclusion quietly specifies which arguments are to be kept implicit and which
should be shown.  In the data constructors for ‘$\ni$’ and ‘$\blacktriangleright$’, you’ll find $Γ,$
$S,$ and $T$ undeclared—their types are inferable from usage by standard techniques [(Damas &
Milner, 1982)](#r2){#rr2 .rr}.  Moreover, the natural deduction rule serves like ‘let’ in the
Hindley-Milner system to indicate the point at which variables should be generalised where possible.
In effect, we may omit declarations for an *initial* segment of parameters to a rule, provided their
types are inferable.

What has happened?  The usual alignment of the implicit-versus-explicit with type-versus-value is so
traditional that you almost forget it’s a design choice.  Dependent types make that choice
untenable, but it’s not the end of the world.


## 3. Renaming and substitution, together

Renaming and substitution are both term traversals, lifting an operation on variables structurally
to the corresponding operation on terms.  Each must perform an appropriate lifting to push an
operation under a $\textsf{lam}$.  Where these operations differ is in the image of variables:
renamings map variables to variables and substitutions map variables to terms.  Here, I abstract the
pattern, showing how to traverse terms, mapping variables to any stuff which supports the necessary
equipment.  What’s stuff?  It’s a type family ‘$\blacklozenge$’ indexed by $\textsf{Ctxt}$ and
$\textsf{Ty}.$  What’s the necessary equipment?  Here it is:

::: {.align-top}
$$
\begin{aligned}
  &\underline{\textrm{data}}\quad
    \frac{\frac{G\ :\ \textsf{Ctxt}\quad T\ :\ \textsf{Ty}}{G\ \blacklozenge\ T\ :\ \star}}
         {\textsf{Kit}(\blacklozenge) : \star}\\[11pt]
  &\underline{\textrm{where}}\quad
    \frac{(\blacklozenge)\quad
          \frac{x\ :\ Γ\ ∋\ T}{vr\ x\ :\ Γ\ \blacklozenge\ T}\quad
          \frac{i\ :\ Γ\ \blacklozenge\ T}{tm\ i\ :\ Γ\ \blacktriangleright\ T}\quad
          \frac{i\ :\ Γ\ \blacklozenge\ T}{wk\ i\ :\ Γ\ ::\ S\ \blacklozenge\ T}}
         {\textsf{kit}\ vr\ tm\ wk : \textsf{Kit}(\blacklozenge)}
\end{aligned}
$$

```
record Kit (_◆_ : Ctxt → Ty → Set) : Set where
  constructor kit
  field
    vr : ∀ {Γ T} (x : Γ ∋ T) → Γ ◆ T
    tm : ∀ {Γ T} (i : Γ ◆ T) → Γ ▶︎ T
    wk : ∀ {Γ S T} (i : Γ ◆ T) → (Γ ∷ S) ◆ T
```
:::

We need ‘$\blacklozenge$’ to support three things: a mapping in from the variables, a mapping out to
the terms, and a weakening map which extends the context.  Renaming will instantiate
‘$\blacklozenge$’ with ‘$\ni$’; for substitution, we may choose ‘$\blacktriangleright$’ instead.
Now we need to show how to traverse terms with any $\textsf{Kit}$, and how to build the
$\textsf{Kit}$s we need.

By the way, you may have noticed that I have nested natural deduction rules in order to declare
parameters which themselves have functional types.  Epigram has ‘hypothetical hypotheses’
hereditarily.  As before, these rules indicate points where variables should be generalised where
possible.  Correspondingly, it is sometimes necessary to insert an (untyped) declaration at an outer
level, in order to suppress generalisation at an inner level.  For example, in the declaration of
$\textsf{kit},$ it’s important that each operation is general with respect to contexts and types,
but they should all apply to a fixed instance of ‘$\blacklozenge$’, hence its explicit declaration.

How do we traverse a term, given a $\textsf{Kit}$?  In general, we have a type-preserving map $τ$
from variables over context $Γ$ to stuff over $Δ$.  We can push that map through terms in a
type-preserving way as follows:

::: {.align-top}
$$
\begin{aligned}
  &\underline{\textrm{let}}
    &&\frac{K : \textsf{Kit}(\blacklozenge)\quad
            Γ, Δ\quad
            \frac{x\ :\ Γ\ ∋\ X}{τ\ x\ :\ Δ\ \blacklozenge\ X}\quad
            t : Γ \blacktriangleright T}
           {\textbf{trav}\ K\ τ\ t : Δ \vartriangleright T}\\[11pt]
  &&&\textbf{trav}\ K\ τ\ t ⇐ \underline{\textrm{rec}}\ t\ \{\\
  &&&\quad\textbf{trav}\ K\ τ\ t ⇐ \underline{\textrm{case}}\ t\ \{\\
  &&&\qquad\textbf{trav}\ K\ τ\ (\textsf{var}\ x) ⇐ \underline{\textrm{case}}\ K\ \{\\
  &&&\qquad\quad\textbf{trav}\ (\textsf{kit}\ vr\ tm\ wk)\ τ\ (\textsf{var}\ x) ⇒
    tm\ (τ\ x)\ \}\\
  &&&\qquad\textbf{trav}\ K\ τ\ (\textsf{lam}\ t') ⇒
    \textsf{lam}\ (\textbf{trav}\ K\ (\textbf{lift}\ K\ τ)\ t')\\
  &&&\qquad\textbf{trav}\ K\ τ\ (\textsf{app}\ f\ s) ⇒
    \textsf{app}\ (\textbf{trav}\ K\ τ\ f)\ (\textbf{trav}\ K\ τ\ s)\ \}\}
\end{aligned}
$$

```
mutual
  trav : ∀ {_◆_ Γ Δ T} (K : Kit _◆_) (τ : ∀ {X} (x : Γ ∋ X) → Δ ◆ X)
           (t : Γ ▶︎ T) → Δ ▶︎ T
  trav (kit vr tm wk) τ (var x)   = tm (τ x)
  trav K              τ (lam t)   = lam (trav K (lift K τ) t)
  trav K              τ (app f s) = app (trav K τ f) (trav K τ s)
```
:::

Epigram programs are tree-structured.  The nodes, marked with ‘$⇐$’ symbols (pronounced ‘by’),
explain how to refine the problem of delivering an output from the inputs, by invoking ‘eliminators’
which specify problem-decomposition strategies, such as structural recursion or case analysis.  The
leaves, marked with ‘$⇒$’ symbols (pronounced ‘return’), indicate the output which the program
should produce in a given case.  Informally, you can imagine that the program only consists of
leaves, defined by pattern matching.  More formally, the program is checked with respect to its
eliminators—each of the $\underline{\textrm{case}}$ nodes is exhaustive, and the recursive calls
are checked to be structural with respect to the parameter indicated in the $\textsf{rec}$ node.
This program is thus seen to be total.

In the $\textsf{var}$ case, our map $τ$ gives us some stuff, which we can turn into a term with some
help from our kit.  The other two cases go with structure, but we shall need to $\textbf{lift}\ τ$
to source and target contexts extended by a bound variable, in order to push it under a binder—we
shall see how to do this in a moment.  The rules of the simply-typed $λ$-calculus are respected
without a squeak!

Note that the ‘patterns’ to the left of ‘$⇐$’ or ‘$⇒$’ were not written by me, but by the editor,
provoked by my choices of eliminator.  The notation may be a touch verbose, but the effort involved
is less than usual.  This somewhat austere notation allows for the possibility of *user-defined*
eliminators, rather than $\underline{\textrm{rec}}$ and $\underline{\textrm{case}},$ a possibility
explored more fully in ‘The view from the left’ [(McBride & McKinna, 2004)](#r5){#rr5-2 .rr}, but it
could readily be tuned to privilege normal behaviour, suppressing $\underline{\textrm{case}}$
eliminators inferable from the constructor symbols in patterns.

But I digress, when I should be writing $\textbf{lift}.$  This just maps the new variable to itself
(or rather, its representation as ‘stuff’), and each old variable to the weakening of its old image.

::: {.align-top}
$$
\begin{aligned}
  &\underline{\textrm{let}}
    &&\frac{K : \textsf{Kit}(\blacklozenge)\quad
            Γ, Δ\quad
            \frac{x\ :\ Γ\ ∋\ X}{τ\ x\ :\ Δ\ \blacklozenge\ X}\quad
            x : Γ :: S \ni T}
           {\textbf{lift}\ K\ τ\ x : Δ :: S\ \blacklozenge\ T}\\[11pt]
  &&&\textbf{lift}\ K\ τ\ x ⇐ \underline{\textrm{case}}\ K\ \{\\
  &&&\quad\textbf{lift}\ (\textsf{kit}\ vr\ tm\ wk)\ τ\ x ⇐ \underline{\textrm{case}}\ x\ \{\\
  &&&\qquad\textbf{lift}\ (\textsf{kit}\ vr\ tm\ wk)\ τ\ \textsf{vz} ⇒ vr\ \textsf{vz}\\
  &&&\qquad\textbf{lift}\ (\textsf{kit}\ vr\ tm\ wk)\ τ\ (\textsf{vs}\ x) ⇒ wk\ (τ\ x)\ \}\}
\end{aligned}
$$

```
  lift : ∀ {_◆_ Γ Δ S T} (K : Kit _◆_) (τ : ∀ {X} (x : Γ ∋ X) → Δ ◆ X)
           (x : (Γ ∷ S) ∋ T) → (Δ ∷ S) ◆ T
  lift (kit vr tm wk) _ vz     = vr vz
  lift (kit vr tm wk) τ (vs x) = wk (τ x)
```
:::

From here, renaming and substitution are easy!  We just need to construct the kits for ‘$\ni$’ and
‘$\blacktriangleright$’ respectively.

::: {.align-top}
$$
\begin{aligned}
  &\underline{\textrm{let}}
    &&\frac{Γ, Δ\quad
            \frac{x\ :\ Γ\ ∋\ X}{ϱ\ x\ :\ Δ\ ∋\ X}\quad
            t : Γ \blacktriangleright T}
           {\textbf{rename}\ ϱ\ t\ : Δ \blacktriangleright T}\\[11pt]
  &&&\textbf{rename}\ ϱ\ t ⇒
    \textbf{trav}\ (\textsf{kit}\ \textbf{id}\ \textsf{var}\ \textsf{vs})\ ϱ\ t
\end{aligned}
$$

```
rename : ∀ {Γ Δ T} (ϱ : ∀ {X} (x : Γ ∋ X) → Δ ∋ X) (t : Γ ▶︎ T) → Δ ▶︎ T
rename ϱ t = trav (kit id var vs) ϱ t
```
:::

The identity function makes variables from variables; the $\textsf{var}$ constructor takes variables
to terms; the $\textsf{vs}$ constructor weakens each variable into an extended context.  Meanwhile,
substitution goes like this:

::: {.align-top}
$$
\begin{aligned}
  &\underline{\textrm{let}}
    &&\frac{Γ, Δ\quad
            \frac{x\ :\ Γ\ ∋\ X}{σ\ x\ :\ Δ\ \blacktriangleright\ X}\quad
            t : Γ \blacktriangleright T}
           {\textbf{subst}\ σ\ t\ : Δ \blacktriangleright T}\\[11pt]
  &&&\textbf{subst}\ σ\ t ⇒
    \textbf{trav}\ (\textsf{kit}\ \textsf{var}\ \textbf{id}\ (\textbf{rename}\ \textsf{vs}))\ σ\ t
\end{aligned}
$$

```
subst : ∀ {Γ Δ T} (σ : ∀ {X} (x : Γ ∋ X) → Δ ▶︎ X) (t : Γ ▶︎ T) → Δ ▶︎ T
subst σ t = trav (kit var id (rename vs)) σ t
```
:::

That is, $\textsf{var}$ makes terms from variables, $\textbf{id}$ takes terms into terms, and a term
is weakened by *renaming* with $\textsf{vs}.$


## References

::: {.references}

1.  ::: {#r1}
    T. Altenkirch and B. Reus (1999) [Monadic presentations of lambda terms using generalized
    inductive types](https://sci-hub.st/10.1007/3-540-48168-0_32),
    *Comp. Sci. Logic*, *Lecture Notes Comp. Sci.*, Vol. 1683, Edited by J. Flum and
    M. Rodriguez-Artalejo, Springer, Berlin, pp. 453–468. [↩](#rr1){.rb} [↩](#rr1-1){.rb}
    :::

2.  ::: {#r2}
    L. Damas and R. Milner (1982) [Principal type-schemes for functional programs
    ](https://sci-hub.st/10.1145/582153.582176),
    *Proc. Symp. Princ. Prog. Lang. (POPL ’82)*, Association for Computing Machinery, New York,
    pp. 207–212. [↩](#rr2){.rb}
    :::

3.  ::: {#r3}
    N. G. de Bruijn (1972) [Lambda calculus notation with nameless dummies: A tool for automatic
    formula manipulation, with application to the Church-Rosser theorem
    ](https://sci-hub.st/10.1016/1385-7258(72)90034-0),
    *Indagationes Mathematicae*, Vol. 75(5), pp. 381–392. [↩](#rr3){.rb}
    :::

4.  ::: {#r4}
    P. Dybjer (1991) [Inductive sets and families in Martin-Löf’s type theory
    ](https://sci-hub.st/10.1017/cbo9780511569807.012),
    *Logical Frameworks*, Edited by G. Huet and G. Plotkin, Cambridge University Press,
    pp. 280–306. [↩](#rr4){.rb}
    :::

5.  ::: {#r5}
    C. McBride and J. McKinna (2004) [The view from the left
    ](https://sci-hub.st/10.1017/S0956796803004829),
    *J. Func. Prog.*, Vol. 14(1), pp. 69–111. [↩](#rr5){.rb} [↩](#rr5-1){.rb} [↩](#rr5-2){.rb}
    :::

:::
