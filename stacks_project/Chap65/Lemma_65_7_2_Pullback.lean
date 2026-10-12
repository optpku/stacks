/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Fibre products of algebraic spaces over a sheaf

If `H` is an fppf sheaf on `Over S` with representable diagonal, and `F`, `G` are algebraic
spaces over `S` equipped with maps of sheaves to `H`, then the sheaf fibre product `F ×_H G` is
an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Functor-of-points pullbacks exist in the presheaf category on schemes over `S`. -/
instance instHasPullbacksFunctorOfPoints {S : Scheme.{u}} :
    HasPullbacks ((Over S)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- The algebraic space `F ×_H G` obtained as the sheaf fibre product of algebraic spaces `F`
and `G` over an fppf sheaf `H` with representable diagonal. -/
def pullbackOver {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) : AlgebraicSpace S :=
  ReasLibPullback.pullbackOver f g hH hΔ

/-- The functor of points of `pullbackOver f g hH hΔ` is the sheaf fibre product of `f` and `g`. -/
@[simp]
theorem pullbackOver_functorOfPoints {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    (pullbackOver f g hH hΔ).functorOfPoints = Limits.pullback f g := sorry

/-- The algebraic space `pullbackOver f g hH hΔ` is an fppf sheaf with representable diagonal
and a representable étale locally-surjective atlas. -/
theorem pullbackOver_spec {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    let X := pullbackOver f g hH hΔ
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The first projection of functors of points for `pullbackOver f g hH hΔ`. -/
def pullbackOverFstNat {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    Limits.pullback f g ⟶ F.functorOfPoints :=
  Limits.pullback.fst f g

/-- The second projection of functors of points for `pullbackOver f g hH hΔ`. -/
def pullbackOverSndNat {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    Limits.pullback f g ⟶ G.functorOfPoints :=
  Limits.pullback.snd f g

/-- The first projection `F ×_H G ⟶ F`. -/
def pullbackOverFst {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOver f g hH hΔ ⟶ F :=
  pullbackOverFstNat f g

/-- The second projection `F ×_H G ⟶ G`. -/
def pullbackOverSnd {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOver f g hH hΔ ⟶ G :=
  pullbackOverSndNat f g

/-- `pullbackOverFstNat f g` is the first projection of the functor-category pullback. -/
theorem pullbackOverFstNat_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    pullbackOverFstNat f g = Limits.pullback.fst f g := sorry

/-- `pullbackOverSndNat f g` is the second projection of the functor-category pullback. -/
theorem pullbackOverSndNat_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H) :
    pullbackOverSndNat f g = Limits.pullback.snd f g := sorry

/-- `pullbackOverFst f g hH hΔ` is the first functor-of-points projection. -/
theorem pullbackOverFst_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOverFst f g hH hΔ = pullbackOverFstNat f g := sorry

/-- `pullbackOverSnd f g hH hΔ` is the second functor-of-points projection. -/
theorem pullbackOverSnd_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    pullbackOverSnd f g hH hΔ = pullbackOverSndNat f g := sorry

/-- The functor-of-points projections exhibit `F ×_H G` as the fibre product of `f` and `g`. -/
theorem pullbackOver_isPullback {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) :
    IsPullback (pullbackOverFstNat f g) (pullbackOverSndNat f g) f g := sorry

/-- The scheme `U ×_H V` obtained from Yoneda sections `a : yoneda.obj U ⟶ F.functorOfPoints`
and `b : yoneda.obj V ⟶ G.functorOfPoints` by pulling back along the maps to `H`. -/
def pullbackOverAtlas {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) : Over S :=
  let ha := Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)
  ha.pullback (b ≫ g)

/-- `pullbackOverAtlas f g hΔ a b` is the representing object of the pullback of `a ≫ f`
along `b ≫ g`. -/
theorem pullbackOverAtlas_eq {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    pullbackOverAtlas f g hΔ a b =
      (Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)).pullback (b ≫ g) := sorry

/-- The projection `U ×_H V ⟶ U` of the representing pullback of the Yoneda sections to `H`. -/
def pullbackOverAtlasFst {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    yoneda.obj (pullbackOverAtlas f g hΔ a b) ⟶ yoneda.obj U :=
  let ha := Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)
  ha.fst (b ≫ g)

/-- The projection `U ×_H V ⟶ V` of the representing pullback of the Yoneda sections to `H`. -/
def pullbackOverAtlasSnd {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    pullbackOverAtlas f g hΔ a b ⟶ V :=
  let ha := Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)
  ha.snd (b ≫ g)

/-- The atlas morphism `U ×_H V ⟶ F ×_H G` induced by the Yoneda sections `a` and `b`. -/
def pullbackOverAtlasHom {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
    (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    yoneda.obj (pullbackOverAtlas f g hΔ a b) ⟶ Limits.pullback f g :=
  Limits.pullback.lift (pullbackOverAtlasFst f g hΔ a b ≫ a)
    (yoneda.map (pullbackOverAtlasSnd f g hΔ a b) ≫ b)
    (((Category.assoc (pullbackOverAtlasFst f g hΔ a b) a f).trans
        ((Functor.relativelyRepresentable.of_diag hΔ (a ≫ f)).w (b ≫ g))).trans
      (Category.assoc (yoneda.map (pullbackOverAtlasSnd f g hΔ a b)) b g).symm)

/-- The square exhibiting `pullbackOverAtlas f g hΔ a b` as the fibre product `U ×_H V`
of the Yoneda sections `a ≫ f` and `b ≫ g` is a pullback. -/
theorem pullbackOverAtlas_isPullback {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints) :
    IsPullback (pullbackOverAtlasFst f g hΔ a b)
      (yoneda.map (pullbackOverAtlasSnd f g hΔ a b)) (a ≫ f) (b ≫ g) := sorry

/-- If `a : yoneda.obj U ⟶ F.functorOfPoints` and `b : yoneda.obj V ⟶ G.functorOfPoints` are
étale and étale-locally surjective, then so is the atlas map `U ×_H V ⟶ F ×_H G`. -/
theorem pullbackOverAtlasHom_spec {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u}
    {F G : AlgebraicSpace S} (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) {U V : Over S}
    (a : yoneda.obj U ⟶ F.functorOfPoints) (b : yoneda.obj V ⟶ G.functorOfPoints)
    (ha_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) a)
    (ha_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a)
    (hb_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) b)
    (hb_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b) :
    MorphismProperty.presheaf (MorphismProperty.over (@Etale))
        (pullbackOverAtlasHom f g hΔ a b) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (pullbackOverAtlasHom f g hΔ a b) := sorry

end AlgebraicGeometry.AlgebraicSpace
