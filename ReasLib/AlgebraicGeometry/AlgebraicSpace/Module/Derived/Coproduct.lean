module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Derived modules on an algebraic space whose cohomology is quasi-coherent admit
coproducts indexed by types in the ambient universe. -/
instance hasCoproducts {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasCoproducts.{u} (DerivedQCoh X) := sorry

/-- The inclusion of derived modules with quasi-coherent cohomology into `D(𝒪_X)`
preserves coproducts indexed by types in the ambient universe. -/
instance inclusionPreservesCoproducts {S : Scheme.{u}} (X : AlgebraicSpace S) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (inclusion X) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
