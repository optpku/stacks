module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Basic

/-!
# Postcomposition of relative morphisms

An over-base morphism induces postcomposition on relative-morphism pairs,
presheaves, and fppf sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X' X : Over B}

namespace Pair

/-- Postcomposition with an over-base morphism preserves the triangle over the base. -/
theorem postcompose_w (f : X' ⟶ X) {T : Over S} (p : Pair Z.hom X'.hom T) :
    (BaseChangeMorphism.toMap p.b ≫ f.left) ≫ X.hom =
      pullback.fst p.a Z.hom ≫ p.a :=
  sorry

/-- Postcompose a relative morphism with an over-base morphism, preserving its test morphism. -/
def postcompose (f : X' ⟶ X) {T : Over S} (p : Pair Z.hom X'.hom T) :
    Pair Z.hom X.hom T :=
  mk p.a (BaseChangeMorphism.ofMap
    (BaseChangeMorphism.toMap p.b ≫ f.left) (postcompose_w f p))

/-- Postcomposition preserves the test morphism of a relative-morphism pair. -/
theorem postcompose_a (f : X' ⟶ X) {T : Over S} (p : Pair Z.hom X'.hom T) :
    (postcompose f p).a = p.a :=
  sorry

/-- The underlying map of a postcomposed pair is the composite of its map with `f.left`. -/
theorem postcompose_toMap (f : X' ⟶ X) {T : Over S} (p : Pair Z.hom X'.hom T) :
    BaseChangeMorphism.toMap (postcompose f p).b =
      BaseChangeMorphism.toMap p.b ≫ f.left :=
  sorry

end Pair

/-- An over-base morphism induces postcomposition on relative-morphism presheaves. -/
def presheafPostcompose (f : X' ⟶ X) : presheaf Z.hom X'.hom ⟶ presheaf Z.hom X.hom where
  app T := TypeCat.ofHom fun p ↦ Pair.postcompose f p
  naturality := sorry

/-- The components of presheaf postcomposition act by postcomposition of pairs. -/
theorem presheafPostcompose_app (f : X' ⟶ X) (T : (Over S)ᵒᵖ)
    (p : Pair Z.hom X'.hom T.unop) :
    (presheafPostcompose f).app T p = Pair.postcompose f p :=
  sorry

/-- An over-base morphism induces postcomposition on relative-morphism fppf sheaves. -/
def postcompose (f : X' ⟶ X) : sheaf Z.hom X'.hom ⟶ sheaf Z.hom X.hom :=
  Sheaf.homEquiv.symm (presheafPostcompose f)

/-- The components of sheaf postcomposition act by postcomposition of pairs. -/
theorem postcompose_app (f : X' ⟶ X) (T : (Over S)ᵒᵖ)
    (p : Pair Z.hom X'.hom T.unop) :
    (postcompose f).hom.app T p = Pair.postcompose f p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
