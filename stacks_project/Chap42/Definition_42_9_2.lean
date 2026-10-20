module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
import StacksCheckRecall

open CategoryTheory TopologicalSpace

universe u

section

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
  [AlgebraicGeometry.UniversallyCatenary S]
  [AlgebraicGeometry.LocallyOfFiniteType f]

/- Definition 42.9.2 (1): The multiplicity of an irreducible component of a closed subscheme is
the length of its stalk as a module over the ambient stalk. -/
@[stacks 02QU]
#check (@AlgebraicGeometry.Scheme.IdealSheafData.componentMultiplicity X
  (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f) :
    (Z : X.IdealSheafData) → genericPoints Z.subscheme → ℕ)

variable (δ : S → ℤ) [IsDimensionFunction δ]

/- Definition 42.9.2 (2): If the `δ`-dimension of a closed subscheme is at most `k`, its
associated `k`-cycle is the multiplicity-weighted sum of its dimension-`k` components. -/
@[stacks 02QU]
#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeCycle f δ :
  (Z : X.IdealSheafData) → (k : ℤ) →
    f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt) →
      AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k)

end
