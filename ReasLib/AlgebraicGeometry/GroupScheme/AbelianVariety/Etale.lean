/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.GroupScheme.MulBy
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Degree

/-!
# Étale multiplication maps on abelian varieties
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AbelianVariety

/-- For a positive-dimensional abelian variety over a field, multiplication by an integer
is étale if and only if that integer is a unit in the field. -/
theorem mulByInt_etale_iff {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
    [AbelianVariety A] (hA : 0 < dimension A) (d : ℤ) :
    Etale (SchemeOverField.mulByInt A d) ↔ IsUnit (d : k) := sorry

end AlgebraicGeometry.AbelianVariety
