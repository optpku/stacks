module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension

@[expose] public section

universe u

open AlgebraicGeometry

#check (AlgebraicGeometry.Scheme.Hom.deltaDimension :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ],
    TopologicalSpace.IrreducibleCloseds X → ℤ)

#check (AlgebraicGeometry.Scheme.Hom.deltaDimension_eq_of_isGenericPoint :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (Z : TopologicalSpace.IrreducibleCloseds X) (ξ : X),
    IsGenericPoint ξ Z →
      f.deltaDimension δ Z = f.relativeDimensionFunction δ ξ)

#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeDeltaDimension :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ], X.IdealSheafData → EInt)

#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeDeltaDimension_def :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData),
    f.closedSubschemeDeltaDimension δ Z =
      ⨆ η : genericPoints Z.subscheme,
        (f.relativeDimensionFunction δ (Z.subschemeι η.1) : EInt))

#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeDeltaDimension_eq_iSup_irreducibleComponents :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData),
    f.closedSubschemeDeltaDimension δ Z =
      ⨆ C : irreducibleComponents Z.subscheme,
        (f.relativeDimensionFunction δ
          (Z.subschemeι (genericPoints.ofComponent C).1) : EInt))
