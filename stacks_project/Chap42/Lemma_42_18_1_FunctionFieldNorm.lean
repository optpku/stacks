module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Norm

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.Hom.inducedFunctionFieldNorm :
  ∀ {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant p],
    X.functionFieldˣ →* Y.functionFieldˣ)

#check (AlgebraicGeometry.Scheme.Hom.inducedFunctionFieldNorm_apply :
  ∀ {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant p]
    (f : X.functionFieldˣ),
    letI : Algebra Y.functionField X.functionField :=
      p.functionFieldAlgebra p.map_genericPoint_eq_of_isDominant
    (p.inducedFunctionFieldNorm f : Y.functionField) =
      Algebra.norm Y.functionField (f : X.functionField))

#check (AlgebraicGeometry.Scheme.Hom.finiteFunctionFieldExtension_of_relativeDimension_eq :
  ∀ {S : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (p : X ⟶ Y) [IsDominant p.left],
    X.hom.relativeDimensionFunction δ (genericPoint X.left) =
      Y.hom.relativeDimensionFunction δ (genericPoint Y.left) →
    p.left.FiniteFunctionFieldExtension)
