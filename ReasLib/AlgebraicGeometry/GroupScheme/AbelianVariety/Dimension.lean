/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.GroupScheme.Dimension

/-!
# Dimensions of abelian varieties
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AbelianVariety

variable {k : Type u} [Field k]

/-- The dimension of an abelian variety, as a natural number. -/
noncomputable def dimension (A : SchemeOverField k) [GrpObj A]
    [AlgebraicGeometry.AbelianVariety A] : ℕ :=
  ENat.toNat ((topologicalKrullDim A.left).unbotD 0)

/-- The natural-number dimension of an abelian variety agrees with its topological Krull
dimension. -/
theorem topologicalKrullDim_eq_dimension (A : SchemeOverField k) [GrpObj A]
    [AlgebraicGeometry.AbelianVariety A] :
    topologicalKrullDim A.left = dimension A := sorry

end AlgebraicGeometry.AbelianVariety
