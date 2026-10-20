module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded Cochain Differential Graded Algebras

This leaf owns the intrinsic bounded-support predicate for cochain differential graded algebras.
The bounds concern the graded pieces themselves, rather than only their homology.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A cochain differential graded algebra is bounded when its graded pieces vanish outside some
finite interval. -/
@[stacks 09RB "bounded cochain differential graded algebras"]
def IsBounded (A : CochainDGAlgebra.{u, v} R) : Prop :=
  CochainComplex.bounded (ModuleCat.{v} R) A.toCochainComplex

/-- DGA boundedness is the canonical bounded object property of its underlying cochain complex. -/
theorem isBounded_iff (A : CochainDGAlgebra.{u, v} R) :
    A.IsBounded ↔ CochainComplex.bounded (ModuleCat.{v} R) A.toCochainComplex := sorry

/-- A bounded cochain differential graded algebra admits lower and upper bounds for its nonzero
graded pieces. -/
theorem IsBounded.exists_bounds {A : CochainDGAlgebra.{u, v} R} (hA : A.IsBounded) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (A.X n) := sorry

end CochainDGAlgebra
