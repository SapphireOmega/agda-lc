\documentclass[a4paper]{article}
\usepackage[margin=2.5cm]{geometry}
\usepackage[parfill]{parskip}

\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amssymb} \usepackage{stmaryrd} \usepackage{csquotes}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\usepackage[colorlinks = true,
            linkcolor = black,
            urlcolor  = blue,
            citecolor = black
            anchorcolor = black]{hyperref}
\usepackage[links]{agda}

%\setmathfont{XITS Math}

\newunicodechar{α}{\ensuremath{\mathnormal\alpha}}
\newunicodechar{β}{\ensuremath{\mathnormal\beta}}
\newunicodechar{η}{\ensuremath{\mathnormal\eta}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{Λ}{\ensuremath{\mathnormal\Lambda}}
\newunicodechar{π}{\ensuremath{\mathnormal\pi}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal\upphi}}
\newunicodechar{←}{\ensuremath{\mathnormal\from}}
\newunicodechar{→}{\ensuremath{\mathnormal\to}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
\newunicodechar{↦}{\ensuremath{\mathnormal\mapsto}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_s}}}
\newunicodechar{₀}{\ensuremath{\mathnormal{_0}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{₄}{\ensuremath{\mathnormal{_4}}}
\newunicodechar{₅}{\ensuremath{\mathnormal{_5}}}
\newunicodechar{₆}{\ensuremath{\mathnormal{_6}}}
\newunicodechar{₇}{\ensuremath{\mathnormal{_7}}}
\newunicodechar{₈}{\ensuremath{\mathnormal{_8}}}
\newunicodechar{₉}{\ensuremath{\mathnormal{_9}}}
\newunicodechar{𝓤}{\ensuremath{\mathnormal{\mathscr{U}}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{⇀}{\ensuremath{\mathnormal\rightharpoonup}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ᵣ}{\ensuremath{\mathnormal{_r}}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{′}{\ensuremath{\mathnormal\prime}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⦂}{\ensuremath{\mathnormal{:}}}
\newunicodechar{₍}{\ensuremath{\mathnormal{(}}}
\newunicodechar{₎}{\ensuremath{\mathnormal{)}}}
\newunicodechar{≣}{\ensuremath{\mathnormal\Xi}}
\newunicodechar{ƛ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{≟}{\ensuremath{\mathnormal=?}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{∷}{\ensuremath{\mathnormal::}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{∨}{\ensuremath{\mathnormal\lor}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^b}}}

\title{λ-Calculus in Agda}
\author{Joris Klaasse Bos}

\begin{document}

\maketitle

\section*{Preface}

This document is a literate Agda program that implements and explains the λ-calculus. I recognise the tremendous irony that herein lies, seeing as we explain λ-calculus through what is essentially not much more than an implementation of dependently typed λ-calculus; it is unlikely that someone who knows Agda should not know λ-calculus already—although they need not be familiar with Church encodings per se. This document should be seen as (very overkill) Theory of Functional Programming lecture notes by someone who is already well versed in the subject.

\tableofcontents

\section*{Prelude}

\begin{code}
module lc where
  open import Agda.Builtin.Equality
  open import Agda.Primitive using (Level; lsuc; lzero; _⊔_) renaming (Set to 𝓤)
  import Relation.Binary.PropositionalEquality as Eq
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (¬?)
  open Eq using (_≡_; refl; cong; cong₂; cong-app; sym; trans)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
  open import Function.Base using (_∘_; _∘₂_; id; _∋_; flip; _$_)
  open import Agda.Builtin.String renaming (primStringEquality to _=ₛ_)
  open import Data.String using (String; _≟_)
  open import Data.List using (List; []; _∷_; _++_; filter)
  open import Data.Bool.Base using (not; if_then_else_; Bool; true; false; _∧_; _∨_)
  open import Data.Maybe using (Maybe; just; nothing; map)

  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ ℓ₉ : Level
    A B C D : 𝓤 ℓ

  -- Finds the first element satisfying the boolean predicate
  findᵇ : (A → Bool) → List A → Maybe A
  findᵇ p []       = nothing
  findᵇ p (x ∷ xs) = if p x then just x else findᵇ p xs

  -- Check if a list of strings contains a certain string
  contains : List String → String → Bool
  contains l x with findᵇ (_=ₛ x) l
  contains l x | nothing = false
  contains l x | just _ = true

  liftM2 : (A → B → C) → Maybe A → Maybe B → Maybe C
  liftM2 f (just x) = map (f x)
  liftM2 f nothing _ = nothing
\end{code}

\pagebreak

\section{λ-Calculus}

The two most important subsections of this section are subsections \ref{terms} and \ref{reduc}. These two subsections define the terms of the λ-calculus and the one computation rule respectively. However, since we use named variables in our definition of λ-terms, and since the name of a variable should not matter for the meaning of a λ-term, we need to add some extra scaffolding to deal with these variable names and possible clashes, and spend some more time on the interpretation of a λ-term. There are other representations of λ-terms possible which do not suffer from these same setbacks, such as \textit{de Bruijn representation}, but these are harder for humans to read. If you want to get a quick overview of λ-calculus, it would suffise to just read the main two subsections, but you will be missing some context which would be necessary to have a solid grasp of λ-calculus.

Strictly speaking we will not be defining the syntax of the λ-calculus in this section. Rather, we represent λ-terms as Agda data types. Agda syntax is quite flexible, so we can make it relatively legible, but really we will just be programming in the abstract syntax tree (AST) directly (for now). We will actually define the syntax in the next section (\ref{syntax}).

\subsection{λ-Terms}\label{terms}

The λ-calculus is an incredibly simple Turing-complete language, i.e.\ it can express any computation a Turing machine can. It has only three introduction rules:

\begin{code}
  data Λ : 𝓤 where
    `    : String → Λ
    _‿_  : Λ → Λ → Λ
    _↦_  : String → Λ → Λ
\end{code}

These three types of terms are known as \textit{variables}, \textit{applications}, and \textit{(λ-)abstractions} respectively. An example of a λ-term could be

\begin{code}
  _ = Λ ∋ ((("a" ↦ ("b" ↦ ` "a")) ‿ ` "x") ‿ ` "y")
\end{code}

There are a lot of parentheses there. To make it a little easier to read, we will add some precedence rules to Agda. Since interpreting \verb#("a" ↦ "b" ↦ ` "a")# as \verb#(("a" ↦ "b") ↦ ` "a")# results in a malformed expression, we will make \verb#_↦_# right-associative. We will make application left-associative so we can read chains of applications from left to right without needing parentheses.

\begin{code}
  infixl 20 _‿_
  infixr 15 _↦_
  infix 20 `
\end{code}

We can now rewrite the previous expression as follows

\begin{code}
  _ = Λ ∋ ("a" ↦ "b" ↦ ` "a") ‿ ` "x" ‿ ` "y"
\end{code}

More examples (from the slides):
\begin{code}
  _ = Λ ∋ ` "v"
  _ = Λ ∋ ` "v" ‿ ` "v"
  _ = Λ ∋ ` "v" ‿ ` "v'"
  _ = Λ ∋ "v" ↦ ` "v" ‿ ` "v'"
  _ = Λ ∋ ` "v" ‿ ("v" ↦ ` "v" ‿ ` "v'")
\end{code}

\subsection{Bound and Free Variables}

We distinguish two types of variables: \textit{bound} and \textit{free} or \textit{unbound}. When we have an abstraction, all occurrences of variables in the body of an abstraction formed from the same string as the first element of said abstraction are called bound. When a variable is not bound by any abstraction, it is called free.

We can write the following function, which returns the names of all the free variables in a λ-term:

\begin{code}
  freeVars : Λ → List String
  freeVars (` x) = x ∷ []
  freeVars (x ‿ y) = freeVars x ++ freeVars y
  freeVars (x ↦ y) = filter (¬? ∘ (_≟ x)) (freeVars y)
\end{code}
For example:

\begin{code}
  _ = freeVars (("a" ↦ "b" ↦ ` "a") ‿ ` "x" ‿ ` "y") ≡ "x" ∷ "y" ∷ [] ∋ refl
  _ = freeVars ("a" ↦ ` "b" ‿ ` "a") ≡ "b" ∷ [] ∋ refl
  -- From the slides:
  _ = freeVars (` "x" ‿ (("x" ↦ ` "x" ‿ ` "y")) ‿ ` "x") ≡ "x" ∷ "y" ∷ "x" ∷ [] ∋ refl
\end{code}

We can also write a function to find all the names of the bound variables.

\begin{code}
  boundVars : Λ → List String
  boundVars (` x) = []
  boundVars (x ‿ y) = (boundVars x) ++ (boundVars y)
  boundVars (x ↦ y) = x ∷ (boundVars y)

  _ = boundVars (("a" ↦ "b" ↦ ` "a") ‿ ` "x" ‿ ` "y") ≡ "a" ∷ "b" ∷ [] ∋ refl
  _ = boundVars ("a" ↦ ` "b" ‿ ` "a") ≡ "a" ∷ [] ∋ refl
  -- From the slides:
  _ = boundVars (` "x" ‿ (("x" ↦ ` "x" ‿ ` "y")) ‿ ` "x") ≡ "x" ∷ [] ∋ refl
\end{code}

Of course, there may be overlap between the results of \verb#freeVars# and \verb#boundVars#, because we are only looking for the names of variables that are bound or free; a name may be used for a bound variable in one subexpression, but a free one in another.

\subsection{Substitution}

When we give computational meaning to λ-terms, we will make use of substitution, so we will invent a function for performing substitutions. Do keep in mind that we are not adding something new to the definition of the λ-calculus, but just defining a function in the meta-language Agda to be able to define the computation rules we will see hereafter. We disallow substitutions that change the binding of a variable to avoid name clashes later on. When a variable is bound multiple times, by convention we say it is bound by the inner most binding abstraction. If we are substituting a variable, but it gets rebound in a subexpression, we do not substitute it in that expression.
\begin{code}
  _[_:=_] : Λ → String → Λ → Maybe Λ
  ` v      [ x := y ] = if v =ₛ x then just y else just (` v)
  e₁ ‿ e₂  [ x := y ] = liftM2 _‿_ (e₁ [ x := y ]) (e₂ [ x := y ])
  (v ↦ e)  [ x := y ] =
    if x =ₛ v
      then just (v ↦ e)  -- Don't do anything when we have an inner rebind
      else if contains (freeVars y) v
        then nothing     -- Would change the binding of a variable
        else map (v ↦_) (e [ x := y ])
\end{code}
Examples:
\begin{code}
  _ =  ("a" ↦ "b" ↦ ` "a") ‿ ` "x" ‿ ` "a" [ "a" := ` "c" ]
       ≡ just (("a" ↦ "b" ↦ ` "a") ‿ ` "x" ‿ ` "c") ∋ refl
  _ =  ("a" ↦ "b" ↦ ` "a" ‿ ` "c") ‿ ` "c" ‿ ` "a" [ "c" := ` "x" ]
       ≡ just (("a" ↦ "b" ↦ ` "a" ‿ ` "x") ‿ ` "x" ‿ ` "a")  ∋ refl
  _ =  ("a" ↦ "b" ↦ ` "c") ‿ ` "c" ‿ ` "a" [ "c" := ` "a" ]
       ≡ nothing ∋ refl
  -- From the slides:
  _ =  (  ∀ {n : Λ} →
            ` "x" ‿ (("x" ↦ ` "x" ‿ ` "y") ‿ ` "x") ["x" := n ]
            ≡ just (n ‿ (("x" ↦ ` "x" ‿ ` "y") ‿ n))
       )  ∋ refl
\end{code}

\subsection{α-Equivalence}

\textit{α-Equivalence}, also known as \textit{α-conversion} and \textit{α-renaming}, states that the name of a variable in a λ-abstraction does not matter; the name is only used to identify which variable is bound to which λ-abstraction. It states we should be able to rename the variable of a λ-abstraction and be left with an expression that is somehow \enquote{the same}. Of course, the restrictions imposed on substitution still apply, and these restrictions avoid name clashes which would actually changing the meaning of a λ-term. We will also add some recursive definitions so it applies α-equivalence to the first λ-abstraction it encounters for ease of use.

\begin{code}
  α-equiv : String → Λ → Maybe Λ
  α-equiv x (v ↦ y) = map (x ↦_) (y [ v := ` x ])  -- Main definition
  α-equiv x (` x₁) = nothing
  α-equiv x (e₁ ‿ e₂) with α-equiv x e₁
  α-equiv x (e₁ ‿ e₂) | nothing = map (e₁ ‿_) (α-equiv x e₂)
  α-equiv x (e₁ ‿ e₂) | just e₁' = just (e₁' ‿ e₂)
\end{code}
Examples:
\begin{code}
  _ =  α-equiv "z" ("a" ↦ "b" ↦ ("c" ↦ ` "a" ‿ ` "c") ‿ ` "b" ‿ ` "a")
       ≡ just ("z" ↦ "b" ↦ ("c" ↦ ` "z" ‿ ` "c") ‿ ` "b" ‿ ` "z") ∋ refl
  _ =  α-equiv "b" ("a" ↦ "b" ↦ ("c" ↦ ` "a" ‿ ` "c") ‿ ` "b" ‿ ` "a")
       ≡ nothing ∋ refl -- Name clash
\end{code}

\subsection{β-Reduction}\label{reduc}

Now we get to the crux of the matter: \textit{β-reduction}. β-Reduction explains how we compute λ-terms, namely, if we apply a λ-abstraction to a λ-term, we can obtain a new λ-term by substituting the term we are applying to for the bound variable in the body of the abstraction. We will also add recursive calls for β-reduction when talking about expressions other than functions, so we will just reduce the first application we encounter.

\begin{code}
  β-reduc : Λ → Maybe Λ
  β-reduc ((v ↦ e₁) ‿ e₂) = e₁ [ v := e₂ ] -- Main definition
  β-reduc (` v) = nothing
  β-reduc (v ↦ e) = map (v ↦_) (β-reduc e)
  β-reduc (e₁ ‿ e₂) with β-reduc e₁
  β-reduc (e₁ ‿ e₂) | nothing = map (e₁ ‿_) (β-reduc e₂)
  β-reduc (e₁ ‿ e₂) | just e₁' = just (e₁' ‿ e₂)
\end{code}
Examples:
\begin{code}
  _ =  β-reduc (("a" ↦ "b" ↦ ` "b") ‿ ` "x")
       ≡ just ("b" ↦ ` "b") ∋ refl
  _ =  β-reduc (("a" ↦ "b" ↦ ` "a") ‿ ` "x")
       ≡ just ("b" ↦ ` "x") ∋ refl
  _ =  β-reduc (("a" ↦ "b" ↦ ` "a") ‿ ` "b")
       ≡ nothing ∋ refl -- Name clash
  -- From the slides:
  _ =  β-reduc (("x" ↦ ` "y" ‿ ` "x") ‿ (` "z" ‿ ` "z"))
       ≡ just (` "y" ‿ (` "z" ‿ ` "z")) ∋ refl
\end{code}

Now that we have given computational meaning to applications of λ-abstractions, we will interchangeably call λ-abstractions (λ-)functions, since now they actually \enquote{function}.

\subsection{Equational Reasoning}

We will create a type which encodes the proposition that some λ-term is reducible to another. These reductions can be done by β-reduction or α-equivalence. Since \verb#β-reduc# and \verb#α-equiv# return \verb#Maybe#'s, we will make the type have a \verb#Maybe# in its right argument.

\begin{code}
  data _→Mλ_ : Λ → Maybe Λ → 𝓤 where
\end{code}

α-Equivalence and β-reduction:

\begin{code}
    α        : ∀ {e : Λ} {v : String}  → e →Mλ α-equiv v e
    β        : ∀ {e : Λ}               → e →Mλ β-reduc e
\end{code}

We will add another reduction rule called \textit{η-reduction}. This is an optional extension to the λ-calculus which we will discuss in the next subsection, so you can ignore it for now.

\begin{code}
    η        : ∀ {e : Λ} {v : String} → (v ↦ e ‿ ` v) →Mλ just e
\end{code}

We will add transitivity so we can chain reductions into one larger reduction, where we keep unwrapping the \verb#Maybe# in between. This also means that we cannot form reductions using \verb#nothing#'s. We also add reflexivity, so doing nothing is also a valid reduction. This will be useful when defining equational reasoning with the type.

\begin{code}
    λ-trans  : ∀ {e₁ e₂ e₃ : Λ}  → e₁ →Mλ just e₂ → e₂ →Mλ just e₃ → e₁ →Mλ just e₃
    λ-refl   : ∀ {e₁ : Λ}        → e₁ →Mλ just e₁
\end{code}

With our definition thus far we can only apply α-equivalence and β-reduction to the first (sub)expression to which they are applicable (as that is how we have defined \verb#α-equiv# and \verb#β-reduc#) in \textit{lazy evaluation order}. This is not so much a problem for β-reduction as it is for α-equivalence, since we might want to apply α-equivalence to a subexpression to show that the whole expression is α-equivalent to another—with β-reduction we can just repeatedly apply it until we are \enquote{done}, where the order does not matter all that much (except if possible infinite computations are involved). To avoid this problem with α-equivalence, we will say that applying a reduction to a subexpression is also a valid reduction.

\begin{code}
    λ-left   : ∀ {e₁ e₂ e₃ : Λ}            → e₁ →Mλ just e₂ → (e₁ ‿ e₃) →Mλ just (e₂ ‿ e₃)
    λ-right  : ∀ {e₁ e₂ e₃ : Λ}            → e₁ →Mλ just e₂ → (e₃ ‿ e₁) →Mλ just (e₃ ‿ e₁)
    λ-body   : ∀ {e₁ e₂ : Λ} {v : String}  → e₁ →Mλ just e₂ → (v ↦ e₁) →Mλ just (v ↦ e₂)
\end{code}

This completes our definition of this type.

We will add a shorthand for \verb#e₁ →Mλ just e₂#.

\begin{code}
  _→λ_ : Λ → Λ → 𝓤
  e₁ →λ e₂ = e₁ →Mλ just e₂
\end{code}

We can now define equational reasoning analogously to equational reasoning with propositional equality in the Agda standard library.

\begin{code}
  infix   5 λ-begin
  infixr  6 step→λ
  infix   7 _λ-end

  λ-begin : Λ → Λ
  λ-begin = id

  step→λ : ∀ (x {y z} : Λ) → y →λ z → x →λ y → x →λ z
  step→λ _ = flip λ-trans

  syntax step→λ x y→λz x→λy = x →⟨ x→λy ⟩ y→λz

  _λ-end : ∀ (e : Λ) → e →λ e
  e λ-end = λ-refl
\end{code}

Examples:

\begin{code}
  _ =  λ-begin  ("a" ↦ "b" ↦ ` "b") ‿ ` "x" ‿ ` "y"
       →⟨ β ⟩   ("b" ↦ ` "b") ‿ ` "y"
       →⟨ β ⟩   ` "y"
       λ-end

  _ =  λ-begin  ("x" ↦ "y" ↦ "z" ↦ ` "x" ‿ ` "z" ‿ ` "y") ‿ ("x" ↦ "y" ↦ ` "x")
       →⟨ β ⟩   "y" ↦ "z" ↦  ("x" ↦ "y" ↦ ` "x") ‿ ` "z" ‿ ` "y"
       →⟨ β ⟩   "y" ↦ "z" ↦  ("y" ↦ ` "z") ‿ ` "y"
       →⟨ β ⟩   "y" ↦ "z" ↦  ` "z"
       →⟨ α {v = "x"} ⟩
                "x" ↦ "z" ↦  ` "z"
       →⟨ λ-body α ⟩
                "x" ↦ "y" ↦  ` "y"
       λ-end

  _ =  λ-begin  ("x" ↦ "y" ↦ "z" ↦ ` "x" ‿ ` "z" ‿ ` "y") ‿ ("x" ↦ "y" ↦ ` "z")
       →⟨ λ-left $ λ-body $ λ-body α ⟩
                ("x" ↦ "y" ↦ "w" ↦ ` "x" ‿ ` "w" ‿ ` "y") ‿ ("x" ↦ "y" ↦ ` "z")
       →⟨ β ⟩   "y" ↦ "w" ↦ ("x" ↦ "y" ↦ ` "z") ‿ ` "w" ‿ ` "y"
       →⟨ β ⟩   "y" ↦ "w" ↦ ("y" ↦ ` "z") ‿ ` "y"
       →⟨ β ⟩   "y" ↦ "w" ↦ ` "z"
       →⟨ α {v = "x"} ⟩
                "x" ↦ "w" ↦ ` "z"
       →⟨ λ-body $ α ⟩
                "x" ↦ "y" ↦ ` "z"
       λ-end
\end{code}

\subsection{η-Reduction}

In the last subsection we added a second reduction rule called \textit{η-Reduction}, which people sometimes extend the lambda calculus with. It states the following:

\verb#     η : ∀ {e : Λ} {v : String} → (v ↦ e ‿ ` v) →λ e#

We will explain its purpose with a little example. Consider the following two λ-terms:

\begin{code}
  _ = Λ ∋ ` "a"
  _ = Λ ∋ "x" ↦ ` "a" ‿ ` "x"
\end{code}

These λ-terms are obviously not the same, nor can either be β-reduced. But what if we apply both to the same argument \verb#` "b"#?

\begin{code}
  _ = Λ ∋ ` "a" ‿ ` "b"
  _ = ("x" ↦ ` "a" ‿ ` "x") ‿ ` "b" →⟨ β ⟩ ` "a" ‿ ` "b" λ-end
\end{code}

They compute to the same expression \verb#` "a" ‿ ` "b"#. In a sense, the first two expressions are the same, because they do the same. This is an instance of \textit{function extensionality}. The second λ-term just wraps \verb#` "a"# in a function, but this unwrapping cannot be undone, or \enquote{reduced} in a sense. It may be desireable to be able to do this, and that is what η-reduction states.

\begin{code}
  _ = "x" ↦ ` "a" ‿ ` "x" →⟨ η ⟩ ` "a" λ-end
\end{code}

\section{Syntax}\label{syntax}

\subsection{Parser Combinators}

\subsection{Core Syntax}

\subsection{Extended Syntax}

\section{Combinatory Logic}

\section{Church Encodings}

\end{document}
