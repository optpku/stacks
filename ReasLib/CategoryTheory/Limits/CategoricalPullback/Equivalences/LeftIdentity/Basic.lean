module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Left identity for categorical pullbacks

The second projection from `(Functor.id C) ⊡ G` is an equivalence. This leaf owns its explicit
inverse and the strict projection equations; equivalence data and computation rules live in
separate leaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory.Limits.CategoricalPullback.LeftIdentity

universe vB vC uB uC

variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace InverseImplementation

/-- Compatibility of the two components of the explicit left-identity inverse. -/
private theorem map_comm (G : B ⥤ C) {x y : B} (f : x ⟶ y) :
    (Functor.id C).map (G.map f) ≫ (Iso.refl (G.obj y)).hom =
      (Iso.refl (G.obj x)).hom ≫ G.map f := sorry

end InverseImplementation

/-- Insert an object into the categorical pullback along `Functor.id C`, using the identity
structural isomorphism. This is the explicit inverse of `π₂ (Functor.id C) G`. -/
def inverse (G : B ⥤ C) : B ⥤ (Functor.id C) ⊡ G where
  obj x :=
    { fst := G.obj x
      snd := x
      iso := Iso.refl _ }
  map {x y} f :=
    { fst := G.map f
      snd := f
      w := InverseImplementation.map_comm G f }

/-- The second projection after the explicit left-identity inverse is the identity functor. -/
theorem inverse.compSnd (G : B ⥤ C) :
    inverse G ⋙ π₂ (Functor.id C) G = Functor.id B := sorry

/-- The first projection after the explicit left-identity inverse is `G`. -/
theorem inverse.compFst (G : B ⥤ C) :
    inverse G ⋙ π₁ (Functor.id C) G = G := sorry

end CategoryTheory.Limits.CategoricalPullback.LeftIdentity
