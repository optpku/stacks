module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension
import StacksCheckRecall

universe u

open AlgebraicGeometry

/- Definition 42.7.6 (1): The `δ`-dimension of an irreducible closed subset is the value of
`f.relativeDimensionFunction δ` at its generic point. -/
@[stacks 02QP] #check (AlgebraicGeometry.Scheme.Hom.deltaDimension :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ],
    TopologicalSpace.IrreducibleCloseds X → ℤ)

/- Definition 42.7.6 (2): The `δ`-dimension of a closed subscheme is the supremum of the
`δ`-dimensions of its irreducible components. -/
@[stacks 02QP] #check (AlgebraicGeometry.Scheme.Hom.closedSubschemeDeltaDimension :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ], X.IdealSheafData → EInt)
