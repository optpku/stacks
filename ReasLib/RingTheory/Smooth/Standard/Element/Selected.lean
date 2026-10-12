/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Standard.Presentation.Selected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Embedding-indexed standard elements of algebras

This leaf owns presentation-independent standard-element predicates and their
generic fixed-presentation constructors.
-/

@[expose] public section

universe u v w t

namespace Algebra

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (R)

/-- An element is elementary standard over `R` if some finite presentation
and equally sized variable and relation embeddings carry elementary data for
it. -/
@[stacks 07C7 "elementary standard elements"]
def IsElementaryStandard (a : A) : Prop :=
  ∃ (ι σ : Type) (_ : Finite ι) (_ : Finite σ)
    (P : Presentation R A ι σ) (c : ℕ)
    (cols : Fin c ↪ ι) (rows : Fin c ↪ σ),
    P.IsElementaryFor a cols rows

/-- An element is strictly standard over `R` if some finite presentation and
finite relation embedding carry strict data for it. -/
@[stacks 07C7 "strictly standard elements"]
def IsStrictlyStandard (a : A) : Prop :=
  ∃ (ι σ : Type) (_ : Finite ι) (_ : Finite σ)
    (P : Presentation R A ι σ) (c : ℕ) (rows : Fin c ↪ σ),
    P.IsStrictlyFor a rows

namespace Presentation.IsElementaryFor

variable {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]

/-- Fixed-presentation elementary data yields the presentation-independent
elementary-standard predicate. -/
@[stacks 07C7 "fixed-presentation elementary data gives an elementary standard element"]
theorem isElementaryStandard
    {P : Presentation R A ι σ} {a : A} {c : ℕ}
    {cols : Fin c ↪ ι} {rows : Fin c ↪ σ}
    (h : P.IsElementaryFor a cols rows) :
    Algebra.IsElementaryStandard R a := sorry

end Presentation.IsElementaryFor

namespace Presentation.IsStrictlyFor

variable {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]

/-- Fixed-presentation strict data yields the presentation-independent
strictly-standard predicate. -/
@[stacks 07C7 "fixed-presentation strict data gives a strictly standard element"]
theorem isStrictlyStandard
    {P : Presentation R A ι σ} {a : A} {c : ℕ}
    {rows : Fin c ↪ σ} (h : P.IsStrictlyFor a rows) :
    Algebra.IsStrictlyStandard R a := sorry

end Presentation.IsStrictlyFor

namespace IsElementaryStandard

/-- An elementary-standard element has a finite-presentation ambient algebra. -/
@[stacks 07C7 "finite-presentation bridge for elementary standard elements"]
theorem finitePresentation
    {a : A} (h : IsElementaryStandard R a) : FinitePresentation R A := sorry

/-- Every elementary-standard element is strictly standard. -/
@[stacks 07EZ "elementary standard implies strictly standard"]
theorem isStrictlyStandard
    {a : A} (h : IsElementaryStandard R a) : IsStrictlyStandard R a := sorry

end IsElementaryStandard

namespace IsStrictlyStandard

/-- A strictly-standard element has a finite-presentation ambient algebra. -/
@[stacks 07C7 "finite-presentation bridge for strictly standard elements"]
theorem finitePresentation
    {a : A} (h : IsStrictlyStandard R a) : FinitePresentation R A := sorry

end IsStrictlyStandard

end Algebra
