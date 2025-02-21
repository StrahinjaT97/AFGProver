#Introduction
# <center>AFG Prover</center>
## Introduction

Welcome to AFG Prover - a growing and expanding interactive and automated theorem prover!

Aim of this project is to create a simple but working interactive theorem prover for first order logic, induction, set theory and modal logic, as well as a basic automated theorem prover for first  order logic. Most of this project's ideas and values are take as inspiration from provers/frameworks such as Vampire, Isabelle-HOL, Coq, Lean ...

As of now (v 0.1) only an interactive theorem prover for FOL has been implemented.

Keep in mind that this is a one man passion project done mostly for boosting my resume.
- - -
## Underlining Structure

Underneath the AFG prover lies the AIS language. An interpreted made-up language that can process the user input into Formula tokens that are then parsed into Sequents. Full documentation for the AIS language is given below.

Every formula presented in AFG prover is considered a "Sequent"; comprised of its assumption part and its goal part. Each part being a formula itself. Although a canonical approach with the use of currying is more pragmatic, I wanted to make my own system, so I ended up using a "Sequent style approach". (One must keep in mind that the use of word 'sequent' is rather loose here)

The main engine of the AFG prover is its set of different interactive provers, each based on different logics or principles. Implemented provers thus far are:
1. Natural Deduction
	- Aristotle (Intuitionistical logic, Propositional logic)
	- Frege (Intuitionistical logic, Propositional logic, First order logic)
	- Godel (Intuitionistical logic, Propositional logic, First order logic, Induction) (In progress)
	- Russel (Intuitionistical logic, Propositional logic, First order logic, Induction, Set theory) (In progress)
2. Sequent Calculus (Planned)
3. Modal logic
	- Kripke (In progress)

All of them are equipped with the same parser, but they interpret the parsed text differently.

The program comes with a built in text-editor that can open and read .ais files
- - -

## AIS Syntax

Goals to be proven are given as "sequents" in AFG. They are of the following style:
$$
\text{assumption1, assumption2} \dots \text{, assumptionN} \vdash \text{goal}
$$
where each $\text{assumption}I$ and goal is a Formula. Note however that the turnstile symbol ($\vdash$) here is interpreted as "to-be-proven" rather than its classical interpretation of "proves"!
Every tactic/rule is applied only to the first assumption in the list of assumption ($\text{assumption1}$), except for tactic _axiom_ (_assumption_) (see below), in the first sequent (see tactic _next_ below).
Whenever the current goal is proven, it is removed from the list of current goals. If there are no more goals to be proven, the phrase "Done." is printed on the screen.
<br />

Each statement to be proven in AFG starts with _lemma_ keyword. There are two variants of this keyword, with and without the colon symbol (:).
If there is no colon symbol the following structure is needed:
- keyword _lemma_ followed by zero or more assumption formulas divided by (;) symbol, followed by a turnstile symbol (|-)  followed by one and only one goal formula.
Example:
```
lemma p; p => q |- q
```
If however, there is a colon symbol following the _lemma_ keyword then assumptions and goal must be split into new lines. Keyword _assume_ is needed to indicate that the following formula is an assumption, while the keyword _show_ is needed to indicate that the following formula is the goal. The order of these combinations of keywords - formulas doesn't matter
Example:
```
lemma:
assume p
show q
assume p => q
```
<br />
Now that we have stated what our initial assumptions and goal is, we encapsulate our proof procedure with keywords _proof_ and _qed_.
Example:
```
lemma a & a |- a
proof
	conjE
	axiom
qed
```
<br />
Between the keyword _proof_ and _qed_ we write out our tactics such that they are separated by any number of whitespaces. For clearance, the use of (;) is permitted, although it is not parsed.
_theorem_ is a syntaxical sugar for _lemma_ keyword.
Specially, keyword _again_, or just the symbol dot (.) applies the previously applied tactic/rule.
Every keyword is converted to all lower case letters so any case style can be used in the construction of the proof!
<br />

Below are listed currently implemented tactics/rules
### Natural deduction

1. Utility rules
$$
\begin{align}
 & \dfrac{a; b; \dots; c; d \vdash goal}{b; \dots; c; d; a \vdash goal}(\text{shiftL, shiftLeft, left})\quad  \quad \dfrac{a; b; \dots; c; d \vdash goal}{d; a; b; \dots; c \vdash goal}(\text{shiftR, shiftRight, right})  \\
 \\
 \\
 & \dfrac{a_{1}; \dots; a_{n} \vdash goal_{1}\quad b_{1}; \dots; b_{n} \vdash goal_{2} \quad \dots \quad c_{1}; \dots; c_{n} \vdash goal_{n}}{b_{1}; \dots; b_{n} \vdash goal_{2} \quad  \dots \quad  c_{1}; \dots; c_{n} \vdash goal_{n} \quad a_{1};\dots; a_{n} \vdash goal_{1} }(\text{next})
\end{align}
$$
2. Axiom rules
$$
\begin{align}
 & \dfrac{\dots ; a ; \dots \vdash a}{\text{Done.}}(\text{axiom, assumption}) \quad \dfrac{a; b; \dots \vdash c}{b; \dots \vdash c}(\text{weak, destroy})
\end{align}
$$
3. Intuitionistical rules
$$
\begin{align}
  \dfrac{a; \dots \vdash b \wedge c}{a; \dots \vdash b \quad  a; \dots \vdash c}(\text{conjI})\quad  \quad  &\dfrac{a \wedge b; \dots \vdash c}{a; b; \dots \vdash c}(\text{conjE}) \\
 \\
  \dfrac{a; \dots \vdash b \vee c}{a; \dots \vdash b}(\text{disjIL, disjI1}) \quad  \quad  &\dfrac{a; \dots \vdash b \vee c}{a; \dots \vdash c}(\text{disjIR, disjI2}) \quad  \quad  \dfrac{a \vee b; \dots \vdash c}{a; \dots \vdash c \quad b; \dots \vdash c}(\text{disjE}) \\
 \\
  \dfrac{a; \dots \vdash b \Rightarrow c}{a; \dots; b \vdash c}(\text{impI}) \quad  \quad &\dfrac{a \Rightarrow b; \dots \vdash c}{\dots \vdash a \quad  b; \dots \vdash c}(\text{impE}) \\
 \\
  \dfrac{a; \dots \vdash b \Leftrightarrow c}{a; \dots \vdash b \Rightarrow c\quad a; \dots \vdash c \Rightarrow b}(\text{iffI})\quad  & \dfrac{a \Leftrightarrow b; \dots \vdash c}{a \Rightarrow b; b \Rightarrow a; \dots \vdash c}(\text{iffE}) \\
 \\
  \dfrac{a; \dots \vdash \neg b}{a; \dots; b \vdash \text{False}}(\text{notI})\quad  &  \dfrac{\neg a; \dots \vdash b}{\dots \vdash a}(\text{notE}) \\
 \\
\end{align}
$$

4. Classical rules
$$
\begin{align}
   \dfrac{a; \dots \vdash b}{a; \dots; \neg b \vdash \text{False}}(\text{ccontra, ccontr}) \quad  & \dfrac{a; \dots \vdash b}{a; \dots; \neg b\vdash b}(\text{classical})
\end{align}
$$

5. Predicate rules
$$
\begin{align}
 & \dfrac{[y_{1}; y_{2};\dots;y_{n}]\quad q; \dots \vdash \forall x_{1} x_{2} \dots x_{n}.(p(x_{1}, x_{2}, \dots, x_{n}) \dots)}{[y_{1}; y_{2};\dots;y_{n}; x_{1}]\quad q; \dots \vdash \forall x_{2} x_{3} \dots x_{n}.(p(x_{1},x_{2},\dots,x_{n})\dots)}(\text{allI, univI}) \\~
 \\~ \\~
  & \dfrac{[y_{1};y_{2};\dots;y_{n}]\quad  \forall x_{1}x_{2}\dots x_{n}.(p(x_{1},x_{2},\dots,x_{n})\dots); \dots \vdash q}{[y_{1};y_{2};\dots;y_{n}]\quad \forall x_{2} \dots x_{n}.(p(t, x_{2}, \dots, x_{n})\dots); \dots \vdash q}(\text{allE }x_{1} \text{ = } t, \, \text{univE } x_{1} \text{ = } t) \\~ \\~ \\~
& \dfrac{[y_{1};y_{2};\dots;y_{n}]\quad q; \dots \vdash \exists x_{1}x_{2} \dots x_{n}.(p(x_{1}, x_{2}, \dots, x_{n}) \dots)}{[y_{1}, y_{2}, \dots, y_{n}]\quad q; \dots \vdash \exists x_{2} \dots x_{n}(p(y_{i}, x_{2}, \dots, x_{n}) \dots)}(\text{exI } x_{1} \text{ = } y_{i})[y_{i} \in \overline{y_{1}, \dots, y_{n}}] \\~
 \\~ \\~
& \dfrac{[y_{1};y_{2};\dots;y_{n}]\quad  \exists x_{1}x_{2} \dots x_{n}.(p(x_{1}, x_{2}, \dots, x_{n})\dots); \dots \vdash q}{[y_{1};y_{2};\dots;y_{n};x_{1}]\quad \exists x_{2}\dots x_{n}.(p(x_{1}, x_{2}, \dots, x_{n})\dots); \dots \vdash q}(\text{exE})
\end{align}
$$

6. Convenience rules
$$
\begin{align}
 & \dfrac{a; \dots \vdash \neg \neg b}{a; \dots \vdash b}(\text{doubleNegI, notnotI}) \quad    \dfrac{\neg \neg a, \dots \vdash b}{a; \dots \vdash b}(\text{doubleNegE, notnotE}) \\
 \\
 & \dfrac{\text{False}; \dots \vdash b}{\text{Done.}}(\text{efq}) \quad \dfrac{a ; \dots; \neg a; \dots \vdash b}{\text{False}; \dots \vdash b}(\text{contraDef, contrDef}) \quad \quad \text{(coming soon)}  \\
 \\
& \dfrac{\forall x_{1}\dots x_{n}.(p(x_{1},\dots,x_{n})\dots);\dots \vdash q}{\neg (\exists x_{1}\dots x_{n}(\neg(p(x_{1}, \dots, x_{n})\dots)));\dots \vdash q}(\text{deMorgan, dm}) \quad   \dfrac{\exists x_{1} \dots x_{n}(p(x_{1}, \dots ,x_{n})\dots);\dots \vdash q}{\neg(\forall x_{1}\dots x_{n}(\neg(p(x_{1},\dots,x_{n})\dots)));\dots \vdash q}(\text{deMorgan, dm})
\end{align}
$$

<br />
<br />

Example of a complete proof:
```
lemma |- p => (q => p)
proof
	impI
	.
	axiom
qed
```
<br />

### Keywords 

List of all AIS keywords with its syntaxical equivalents:
- _lemma_ / _theorem_
- _lemma:_ / _theorem:_
- _|-_ / _proves_
- _assume_
- _show_
- _proof_
- _qed_
- _next_
- _shiftL_ / _shiftLeft_ / _left_
- _shiftR_ / _shiftRight_ / _right_
- _again_ / _._
- _axiom_ / _assumption_
- _weak_ / _destroy_
- _conjI_ 
- _conjE_
- _disjIL_ / _disjI1_
- _disjIR_ / _disjI2_
- _disjE_
- _impI_
- _impE_
- _iffI_
- _iffE_
- _notI_
- _notE_
- _ccontra_ / _ccontr_
- _classical_
- _allI_ / _univI_
- _allE_ / _univE_
- _exI_
- _exE_
- _doubleNegI_ / _notnotI_
- _doubleNegE_ / _notnotE_
- _deMorgan_ / _dm_
<br />

Below is the list of all logical constants, connectives and a regex for constructing variables or quantified formulas.
Every logical connective can be represented either by its designated symbol or its keyword!
- True
- False
- & / _and_
- | / _or_
- => / _implies_
- <=> / _iff_ / _equiv_
- = / _equals_
- ~ / _not_ / _neg_
- ! / _univ_
- ? / _exists_
- $P$ / _possibly_ / 
- $N$ / _necessarily_ / 
- term = ([a-z] | [A-M, O, Q-Z]) ([a-z] | [A-Z] | [0-9])*
- predicate = term " "* "(" " "* term ("," " "* term)* " "* ")"
- quantified_formula = (! | ? | $P$ | $N$ ) (term " "+)+ ".(" formula ")"

- - - 
## Closing notes

The text editor comes with a set of example lemmas that can be loaded in immediately. As the nature demands it, the proof of these lemmas is left as an exercise to the user.