module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Differentials

/-!
# Pullback comparison for relative differentials of algebraic spaces

A commutative square of algebraic spaces has a unique pullback comparison on relative
differential sheaves, characterized by its action on local universal differentials.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}}
variable {X X' Y Y' : AlgebraicSpace S}
variable (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
variable (sq : f ≫ h = h' ≫ g)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.existsUnique_comparison
  f g h h' sq :
  ∃! tau : (Modules.pullback f).obj (Hom.relativeDifferentials h) ⟶
      Hom.relativeDifferentials h',
    AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.IsComparison f h h' tau)
