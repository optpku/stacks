module

public import Mathlib.AlgebraicGeometry.Stalk
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Stalk spectra of schematic charts

A scheme `T` over `S` and a point `t` of `T` determine the object
`Spec(𝒪_{T.left, t})` of `Over S`, together with the morphism into an
algebraic space obtained by composing with a chart `ofOver T ⟶ X`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The object `Spec(𝒪_{T.left, t})` of `Over S`, with structure morphism
`T.left.fromSpecStalk t ≫ T.hom`. -/
def specStalkOver {S : Scheme.{u}} (T : Over S) (t : T.left) : Over S :=
  Over.mk (T.left.fromSpecStalk t ≫ T.hom)

/-- `specStalkOver T t` is `Over.mk` of the composite structure morphism. -/
theorem specStalkOver_eq {S : Scheme.{u}} (T : Over S) (t : T.left) :
    specStalkOver T t = Over.mk (T.left.fromSpecStalk t ≫ T.hom) :=
  sorry

/-- The underlying scheme of `specStalkOver T t` is `Spec (T.left.presheaf.stalk t)`. -/
theorem specStalkOver_left {S : Scheme.{u}} (T : Over S) (t : T.left) :
    (specStalkOver T t).left = Spec (T.left.presheaf.stalk t) :=
  sorry

/-- The morphism `Spec(𝒪_{T.left, t}) ⟶ T` in `Over S`. -/
def specStalkOverHom {S : Scheme.{u}} (T : Over S) (t : T.left) :
    specStalkOver T t ⟶ T :=
  Over.homMk (T.left.fromSpecStalk t) rfl

/-- `specStalkOverHom T t` is `Over.homMk` of `T.left.fromSpecStalk t`. -/
theorem specStalkOverHom_eq {S : Scheme.{u}} (T : Over S) (t : T.left) :
    specStalkOverHom T t = Over.homMk (T.left.fromSpecStalk t) rfl :=
  sorry

/-- The underlying scheme morphism of `specStalkOverHom T t` is `T.left.fromSpecStalk t`. -/
theorem specStalkOverHom_left {S : Scheme.{u}} (T : Over S) (t : T.left) :
    (specStalkOverHom T t).left = T.left.fromSpecStalk t :=
  sorry

/-- The morphism `Spec(𝒪_{U, u}) ⟶ X` of algebraic spaces over `S` obtained from a
chart `ι : ofOver U ⟶ X`. -/
def fromSpecStalk {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (ι : ofOver U ⟶ X) (u : U.left) : ofOver (specStalkOver U u) ⟶ X :=
  ofOverMap (specStalkOverHom U u) ≫ ι

/-- `fromSpecStalk ι u` is the chart postcomposed with the algebraic-space image of
`specStalkOverHom`. -/
theorem fromSpecStalk_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (ι : ofOver U ⟶ X) (u : U.left) :
    fromSpecStalk ι u = ofOverMap (specStalkOverHom U u) ≫ ι :=
  sorry

/-- Postcomposing a chart postcomposes `fromSpecStalk`. -/
theorem fromSpecStalk_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U : Over S}
    (ι : ofOver U ⟶ X) (u : U.left) (f : X ⟶ Y) :
    fromSpecStalk (ι ≫ f) u = fromSpecStalk ι u ≫ f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
