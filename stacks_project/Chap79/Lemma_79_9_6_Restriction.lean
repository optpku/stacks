module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Lemma_78_17_1_Restriction
public import stacks_project.Chap79.Situation_79_9_2_OnField

/-!
# Field-homomorphism restriction of groupoids in algebraic spaces

This module records the restriction of a groupoid in algebraic spaces along an
explicit field homomorphism `ι : k →+* k'` of its object space, together with
the induced identification of the restricted object space with `Spec(k')`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The morphism `Spec(k') ⟶ U` of algebraic spaces induced by a field homomorphism
`ι : k →+* k'` and an identification `U ≅ Spec(k)` over `S`. -/
abbrev fieldRestrictionOfHomMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    ofOver (Over.mk (Spec.map (CommRingCat.ofHom ι) ≫ σ)) ⟶ G.U.left :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom ι)) rfl ≫ eU.inv

/-- The object space over `B` obtained by extending the field of objects along `ι`. -/
abbrev fieldRestrictionOfHomOver {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    Over B :=
  Over.mk (fieldRestrictionOfHomMap G eU ι ≫ G.U.hom)

/-- The canonical morphism over `B` from the field-homomorphism object space to the
original object space. -/
abbrev fieldRestrictionOfHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    fieldRestrictionOfHomOver G eU ι ⟶ G.U :=
  Over.homMk (fieldRestrictionOfHomMap G eU ι) rfl

/-- The underlying algebraic-space map of `fieldRestrictionOfHom` is
`fieldRestrictionOfHomMap`. -/
theorem fieldRestrictionOfHom_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    (fieldRestrictionOfHom G eU ι).left = fieldRestrictionOfHomMap G eU ι :=
  sorry

/-- The restricted object space is `Spec(k')` as an algebraic space over `S`. -/
theorem fieldRestrictionOfHomOver_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    (fieldRestrictionOfHomOver G eU ι).left =
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom ι) ≫ σ)) :=
  sorry

/-- Restriction along a field homomorphism of the object space remains a groupoid on a
field. -/
instance instIsOnField_fieldRestrictionOfHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    IsOnField (G.pullback (fieldRestrictionOfHom G eU ι))
      (Spec.map (CommRingCat.ofHom ι) ≫ σ) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
