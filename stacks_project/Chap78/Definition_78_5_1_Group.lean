module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group

/-! Compatibility checks for the group algebraic-space API. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

#check (AlgebraicGeometry.AlgebraicSpace.instCartesianMonoidalCategoryOver :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S), CartesianMonoidalCategory (Over B))
#check (AlgebraicGeometry.GroupAlgebraicSpace.schemePoints_group :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (T : Over S)
    (t : AlgebraicSpace.ofOver T ⟶ B), Group (Over.mk t ⟶ G.X))
#check (AlgebraicGeometry.GroupAlgebraicSpace.hom_iff_isMonHom :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G G' : GroupAlgebraicSpace B}
    (ψ : G.X ⟶ G'.X), (∃ φ : G ⟶ G', φ.hom.hom = ψ) ↔ IsMonHom ψ)
#check (AlgebraicGeometry.GroupAlgebraicSpace.hom_iff_schemePoints :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G G' : GroupAlgebraicSpace B}
    (ψ : G.X ⟶ G'.X),
      IsMonHom ψ ↔
        ∀ (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B),
          ∀ a b : Over.mk t ⟶ G.X, (a ≫ ψ) * (b ≫ ψ) = (a * b) ≫ ψ)
