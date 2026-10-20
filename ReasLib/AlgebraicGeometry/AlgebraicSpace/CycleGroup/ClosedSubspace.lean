module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A locally finite cycle belongs to the degree-`k` cycle group if and only if
every integral closed subspace whose generic point has nonzero coefficient has
`δ`-dimension `k`. -/
theorem mem_cycleGroup_iff_closedSubspaceDeltaDimension
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ Hom.cycleGroup f δ k ↔
      ∀ (Z : ClosedSubspace X) (hZ : IsIntegral Z.X) (ξ : Points X),
        IsGenericPoint ξ Z.pointsSet → α ξ ≠ 0 →
          Hom.closedSubspaceDeltaDimension f δ Z = (k : EInt) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
