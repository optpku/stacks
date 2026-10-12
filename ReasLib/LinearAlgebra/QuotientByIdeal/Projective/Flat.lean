/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective

/-!
# Projectivity from a flat nilpotent quotient

This leaf owns the nilpotent-thickening criterion that upgrades a flat module to a projective
module once its quotient by the nilpotent ideal is projective.
-/

@[expose] public section

universe u v

namespace Module.Projective

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

/-- A flat module is projective when its quotient by a nilpotent ideal is projective. -/
@[stacks 05CG "flat projectivity across a nilpotent quotient"]
theorem of_flat_of_quotient_of_isNilpotent
    (hI : IsNilpotent I)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Projective R M := sorry

end Module.Projective
