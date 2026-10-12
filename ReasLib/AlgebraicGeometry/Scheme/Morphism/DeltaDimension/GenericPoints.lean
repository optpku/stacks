/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A point of a closed subscheme that attains an upper bound for its `δ`-dimension is a
generic point of an irreducible component. -/
theorem mem_genericPoints_of_closedSubschemeDeltaDimension_le
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData)
    (ξ : Z.subscheme) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt))
    (hξ : f.relativeDimensionFunction δ (Z.subschemeι ξ) = k) :
    ξ ∈ genericPoints Z.subscheme := sorry

end AlgebraicGeometry.Scheme.Hom
