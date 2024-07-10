---
author:  C. McBride
hauthor: Conor McBride
year:    2006
title:   Type-preserving renaming and substitution
htitle:  Type-preserving<br>renaming and substitution
lang:    en
wip:     yes
card:
  - C. McBride (2006)
  - '[Type-preserving renaming and substitution
    ](http://strictlypositive.org/ren-sub.pdf)'
  - Manuscript.
todo:
  - DOI missing
---


```
-- Not yet re-mechanised by Miëtek Bak
-- TODO: Epigram code fragments

module mi.McBride2006 where

⋆ : Set _
⋆ = Set
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
   traversal operation is structually recursive, hence clearly total.

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

~~~
TODO
~~~

```
data Ty :
          ---
          ⋆ where

  • :
      --
      Ty

  _▷_ : (S T : Ty)
        ----------
           → Ty




data Ctxt :
            ---
            ⋆ where

  ε :
      ----
      Ctxt

  _∷_ : (Γ : Ctxt) → (S : Ty)
        ---------------------
               → Ctxt




data _∋_ : (Γ : Ctxt) → (T : Ty)
           ---------------------
                   → ⋆         where

  vz : ∀{Γ S}
              -------------
              → (Γ ∷ S) ∋ S

  vs : ∀{Γ S T}    → Γ ∋ T
                -------------
                → (Γ ∷ S) ∋ T




data _▶︎_ : (Γ : Ctxt) → (T : Ty)
           ---------------------
                   → ⋆         where

  var : ∀{Γ T} → (x : Γ ∋ T)
               -------------
                  → Γ ▶︎ T

  lam : ∀{Γ S T} → (t : (Γ ∷ S) ▶︎ T)
                 -------------------
                    → Γ ▶︎ (S ▷ T)

  app : ∀{Γ S T} → (f : Γ ▶︎ (S ▷ T)) → (s : Γ ▶︎ S)
                 ---------------------------------
                             → Γ ▶︎ T
```

This may seem like overkill for ‘simple’ definitions like $\textsf{Ty}$ (for simple types) and
$\textsf{Ctxt}$ (for contexts—reversed lists of simple types), which you might imagine writing
grammar-style, like this:

$$
\begin{aligned}
  \underline{\textrm{data}}\ \textsf{Ty}  &=
    \bullet\ |\ \textsf{Ty} \vartriangleright \textsf{Ty} \\
  \underline{\textrm{data}}\ \textsf{Ctx} &=
    ε\ |\ \textsf{Ctxt} :: \textsf{Ty}
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
$S,$ and $T$ undeclared—their types are inferrable from usage by standard techniques [(Damas &
Milner, 1982)](#r2){#rr2 .rr}.  Moreover, the natural deduction rule serves like ‘let’ in the
Hindley-Milner system to indicate the point at which variables should be generalised where possible.
In effect, we may omit declarations for an *initial* segment of parameters to a rule, provided their
types are inferrable.

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

~~~
TODO
~~~

```
record Kit   (_◆_ : (Γ : Ctxt) → (T : Ty)
                    ---------------------
                           → ⋆         )
           : -----------------------------
                          ⋆              where

  constructor kit
  field

    vr : ∀{Γ T} → (x : Γ ∋ T)
                -------------
                   → Γ ◆ T

    tm : ∀{Γ T} → (i : Γ ◆ T)
                -------------
                   → Γ ▶︎ T

    wk : ∀{Γ S T} → (i : Γ ◆ T)
                  -------------
                  → (Γ ∷ S) ◆ T
```

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

~~~
TODO
~~~

```
lift : ∀{_◆_ Γ Δ S T} → (K : Kit _◆_) → (τ : ∀{X} → (x : Γ ∋ X)
                                                  -------------
                                                     → Δ ◆ X   ) → (x : (Γ ∷ S) ∋ T)
                      --------------------------------------------------------------
                                              → (Δ ∷ S) ◆ T

lift (kit vr _ _) _ vz     = vr vz
lift (kit _ _ wk) τ (vs x) = wk (τ x)


trav : ∀{_◆_ Γ Δ T} → (K : Kit _◆_) → (τ : ∀{X} → (x : Γ ∋ X)
                                                -------------
                                                   → Δ ◆ X   ) → (t : Γ ▶︎ T)
                    --------------------------------------------------------
                                            → Δ ▶︎ T

trav (kit _ tm _) τ (var x)   = tm (τ x)
trav K            τ (lam t)   = lam (trav K (lift K τ) t)
trav K            τ (app f s) = app (trav K τ f) (trav K τ s)
```

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
help from our kit.  The other two cases go with structure, but we shall need to $\textbf{lift } τ$
to source and target contexts extended by a bound variable, in order to push it under a binder—we
shall see how to do this in a moment.  The rules of the simply-typed $λ$-calculus are respected
without a squeak!

Note that the ‘patterns’ to the left of ‘$⇐$’ or ‘$⇒$’ were not written by me, but by the editor,
provoked by my choices of eliminator.  The notation may be a touch verbose, but the effort involved
is less than usual.  This somewhat austere notation allows for the possibility of *user-defined*
eliminators, rather than $\underline{\textrm{rec}}$ and $\underline{\textrm{case}},$ a possibility
explored more fully in ‘The view from the left’ (McBride & McKinna, 2004), but it could readily be
tuned to privilege normal behaviour, suppressing $\underline{\textrm{case}}$ eliminators inferrable
from the constructor symbols in patterns.

But I digress, when I should be writing $\textbf{lift}.$  This just maps the new variable to itself
(or rather, its representation as ‘stuff’), and each old variable to the weakening of its old image.

~~~
TODO
~~~

From here, renaming and substitution are easy!  We just need to construct the kits for ‘$\ni$’ and
‘$\blacktriangleright$’ respectively.

~~~
TODO
~~~

```
rename : ∀{Γ Δ T} → (ρ : ∀{X} → (x : Γ ∋ X)
                              -------------
                                 → Δ ∋ X   ) → (t : Γ ▶︎ T)
                  ----------------------------------------
                                  → Δ ▶︎ T

rename ρ t = trav (kit (λ x → x) var vs) ρ t
```

The identity function makes variables from variables; the $\textsf{var}$ constructor takes variables
to terms; the $\textsf{vs}$ constructor weakens each variable into an extended context.  Meanwhile,
substitution goes like this:

~~~
TODO
~~~

```
subst : ∀{Γ Δ T} → (σ : ∀{X} → (x : Γ ∋ X)
                             -------------
                                → Δ ▶︎ X   ) → (t : Γ ▶︎ T)
                 ----------------------------------------
                                 → Δ ▶︎ T

subst σ t = trav (kit var (λ x → x) (rename vs)) σ t
```

That is, $\textsf{var}$ makes terms from variables, $\textbf{id}$ takes terms into terms, and a term
is weakened by *renaming* with $\textsf{vs}.$


## References

::: {.references}

1.  ::: {#r1}
    T. Altenkirch and B. Reus (1999) [Monadic presentations of lambda-terms using generalized
    inductive types](),
    …. [↩](#rr1){.rb} [↩](#rr1-1){.rb}
    :::

2.  ::: {#r2}
    L. Damas and R. Milner (1982) [Principal type-schemes for functional programming languages
    ](),
    …. [↩](#rr2){.rb}
    :::

3.  ::: {#r3}
    N. G. de Bruijn (1972) [Lambda calculus notation with nameless dummies: A tool for automatic
    formula manipulation](),
    …. [↩](#rr3){.rb}
    :::

4.  ::: {#r4}
    P. Dybjer (1991) [Inductive sets and families in Martin-Löf’s type theory
    ](),
    …. [↩](#rr4){.rb}
    :::

5.  ::: {#r5}
    C. McBride and J. McKinna (2004) [The view from the left
    ](),
    …. [↩](#rr5){.rb} [↩](#rr5-1){.rb}
    :::

:::
