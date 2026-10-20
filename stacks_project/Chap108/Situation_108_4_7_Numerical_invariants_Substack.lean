module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Compatibility bridge for the numerical full subcategory and its groupoid fibration. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoidsNumerical :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ),
      (∀ i, ModuleDerived.IsPerfect (E i)) →
      FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))

/- The canonical inclusion into the coherent-family groupoid fibration. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.ι :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
      (hE : ∀ i, ModuleDerived.IsPerfect (E i)),
      CohStack.toGroupoidsNumerical f E P hE ⟶ CohStack.toGroupoids f)
