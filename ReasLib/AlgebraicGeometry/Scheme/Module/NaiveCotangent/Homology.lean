/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent

/-!
# Homology of naive cotangent complexes of scheme morphisms
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- The homology of the naive cotangent complex of a scheme morphism vanishes outside
degrees `-1` and `0`. -/
theorem homology_isZero_of_ne_zero_or_negOne
    {X Y : Scheme.{u}} (f : X ⟶ Y) (i : ℤ) (hi_zero : i ≠ 0) (hi_negOne : i ≠ -1) :
    IsZero ((NL[f.toShHom]).homology i) := sorry

/-- Every homology sheaf of the naive cotangent complex of a scheme morphism is
quasi-coherent. -/
@[instance]
theorem homology_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y) (i : ℤ) :
    ((NL[f.toShHom]).homology i).IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
