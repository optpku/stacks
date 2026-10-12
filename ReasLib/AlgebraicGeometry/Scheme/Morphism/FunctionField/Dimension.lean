/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Equality of the generic-point relative dimensions makes the function-field extension induced
by a dominant morphism finite. -/
theorem finiteFunctionFieldExtension_of_relativeDimension_eq
    {S : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (p : X ⟶ Y) [IsDominant p.left]
    (h : X.hom.relativeDimensionFunction δ (genericPoint X.left) =
      Y.hom.relativeDimensionFunction δ (genericPoint Y.left)) :
    p.left.FiniteFunctionFieldExtension := sorry

end AlgebraicGeometry.Scheme.Hom
