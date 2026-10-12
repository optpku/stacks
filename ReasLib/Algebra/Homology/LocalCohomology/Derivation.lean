/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.LocalCohomology
public import ReasLib.Algebra.Module.DifferentialOperator.Derivation

@[expose] public section

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Every absolute derivation of a commutative ring admits an additive operator on each
local cohomology module supported in a finitely generated ideal satisfying its Leibniz rule. -/
theorem existsDerivationOperator (I : Ideal A) (hI : I.FG)
    (θ : Derivation ℤ A A) (i : ℕ) :
    ∃ D : Module.End ℤ ((localCohomology I i).obj (ModuleCat.of A A)),
      D.IsModuleDerivation θ := sorry

end Ideal.LocalCohomology
