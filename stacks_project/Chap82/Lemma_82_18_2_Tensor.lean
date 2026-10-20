module

public import stacks_project.Chap82.Definition_82_18_1_ChernCap

/-!
# Tensor and unit identities for first-Chern cap on algebraic spaces

These are properties of the canonical first-Chern cap with values in the Chow
group defined by locally finite rational equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- First-Chern cap is additive in the invertible sheaf: intersecting a
`(k + 1)`-cycle with `c1(L ⊗ N)` equals the sum of the intersections with
`c1(L)` and `c1(N)` in `CH_k(X)`. -/
theorem firstChernClassCap_tensor (L N : X.Modules) [isInvertibleObject L]
    [isInvertibleObject N] (k : ℤ) (α : cycleGroup f δ (k + 1)) :
    firstChernClassCap f δ L k α + firstChernClassCap f δ N k α =
      firstChernClassCap f δ (L ⊗ N) k α :=
  sorry

/-- First-Chern cap against the structure sheaf vanishes: intersecting any
`(k + 1)`-cycle with `c1(𝟙_ X.Modules)` is `0` in `CH_k(X)`. -/
theorem firstChernClassCap_tensorUnit (k : ℤ) (α : cycleGroup f δ (k + 1)) :
    firstChernClassCap f δ (𝟙_ X.Modules) k α = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
