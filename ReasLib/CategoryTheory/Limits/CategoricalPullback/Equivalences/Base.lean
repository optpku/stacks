/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EqToHom
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.QuasiInverse
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic

/-!
# Common-base transport of categorical pullbacks

Change of the common cospan base, its explicit inverse along an equivalence, and projection
comparison APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! ### Equivalence-invariance of the categorical pullback `⊡`

Mathlib lists "Full equivalence-invariance of the notion (follows from suitable 2-functoriality)"
of `CategoricalPullback` as a TODO. The congruences below give useful concrete cases: invariance
under postcomposing both legs with an equivalence of the common base, under natural isomorphisms
of the two legs, and under equivalences of the endpoint domains. They are stated directly for the
explicit `(a, b, F a ≅ G b)` model. -/

section CatPullbackCongr

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- The inverse cospan transformation to common base change along an equivalence. Its two square
isomorphisms are obtained from the unit of the base equivalence. -/
def BaseChange.inverseTransform
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    CatCospanTransform (F ⋙ eB.functor) (G ⋙ eB.functor) F G :=
  CatCospanTransform.ofIso
    (Functor.associator F eB.functor eB.inverse ≪≫
      Functor.isoWhiskerLeft F eB.unitIso.symm ≪≫
        Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
    (Functor.associator G eB.functor eB.inverse ≪≫
      Functor.isoWhiskerLeft G eB.unitIso.symm ≪≫
        Functor.rightUnitor G ≪≫ (Functor.leftUnitor G).symm)

/-- The explicit inverse to common base change along an equivalence. -/
noncomputable def BaseChange.inverse
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor) ⥤ F ⊡ G :=
  CategoricalPullback.map (BaseChange.inverseTransform F G eB)

/-- Inverse base change retains the left endpoint object. -/
@[simp]
theorem BaseChange.inverse.obj.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.inverse F G eB).obj x).fst = x.fst := sorry

/-- Inverse base change retains the right endpoint object. -/
@[simp]
theorem BaseChange.inverse.obj.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.inverse F G eB).obj x).snd = x.snd := sorry

/-- Inverse base change applies the inverse base functor to the structural isomorphism and
conjugates by the unit of the base equivalence. -/
@[simp]
theorem BaseChange.inverse.obj.iso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.inverse F G eB).obj x).iso =
      eB.unitIso.app (F.obj x.fst) ≪≫
        eB.inverse.mapIso x.iso ≪≫
          (eB.unitIso.app (G.obj x.snd)).symm := sorry

/-- Inverse base change retains the left component of a morphism. -/
@[simp]
theorem BaseChange.inverse.hom.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    {x y : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)} (f : x ⟶ y) :
    ((BaseChange.inverse F G eB).map f).fst = f.fst := sorry

/-- Inverse base change retains the right component of a morphism. -/
@[simp]
theorem BaseChange.inverse.hom.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    {x y : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)} (f : x ⟶ y) :
    ((BaseChange.inverse F G eB).map f).snd = f.snd := sorry

/-- Left-square coherence for the unit of explicit inverse base change. -/
theorem BaseChange.transformUnitIso.leftCoherence
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (CatCospanTransform.id F G).squareLeft.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 A₀)).inv F =
      Functor.whiskerLeft F eB.unitIso.hom ≫
        ((postcompose.transform F G eB.functor).comp
          (BaseChange.inverseTransform F G eB)).squareLeft.iso.hom := sorry

/-- Right-square coherence for the unit of explicit inverse base change. -/
theorem BaseChange.transformUnitIso.rightCoherence
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (CatCospanTransform.id F G).squareRight.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 B₀)).inv G =
      Functor.whiskerLeft G eB.unitIso.hom ≫
        ((postcompose.transform F G eB.functor).comp
          (BaseChange.inverseTransform F G eB)).squareRight.iso.hom := sorry

/-- The unit comparison between the identity cospan transformation and common base change
followed by its explicit inverse. -/
noncomputable def BaseChange.transformUnitIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    CatCospanTransform.id F G ≅
      (postcompose.transform F G eB.functor).comp
        (BaseChange.inverseTransform F G eB) :=
  CatCospanTransform.mkIso (Functor.leftUnitor (𝟭 A₀)).symm
    (Functor.leftUnitor (𝟭 B₀)).symm eB.unitIso
    (BaseChange.transformUnitIso.leftCoherence F G eB)
      (BaseChange.transformUnitIso.rightCoherence F G eB)

/-- Left-square coherence for the counit of explicit inverse base change. -/
theorem BaseChange.transformCounitIso.leftCoherence
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    ((BaseChange.inverseTransform F G eB).comp
        (postcompose.transform F G eB.functor)).squareLeft.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 A₀)).hom
          (F ⋙ eB.functor) =
      Functor.whiskerLeft (F ⋙ eB.functor) eB.counitIso.hom ≫
        (CatCospanTransform.id
          (F ⋙ eB.functor) (G ⋙ eB.functor)).squareLeft.iso.hom := sorry

/-- Right-square coherence for the counit of explicit inverse base change. -/
theorem BaseChange.transformCounitIso.rightCoherence
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    ((BaseChange.inverseTransform F G eB).comp
        (postcompose.transform F G eB.functor)).squareRight.iso.hom ≫
        Functor.whiskerRight (Functor.leftUnitor (𝟭 B₀)).hom
          (G ⋙ eB.functor) =
      Functor.whiskerLeft (G ⋙ eB.functor) eB.counitIso.hom ≫
        (CatCospanTransform.id
          (F ⋙ eB.functor) (G ⋙ eB.functor)).squareRight.iso.hom := sorry

/-- The counit comparison between inverse base change followed by base change and the identity
target cospan transformation. -/
noncomputable def BaseChange.transformCounitIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.inverseTransform F G eB).comp
        (postcompose.transform F G eB.functor) ≅
      CatCospanTransform.id (F ⋙ eB.functor) (G ⋙ eB.functor) :=
  CatCospanTransform.mkIso (Functor.leftUnitor (𝟭 A₀))
    (Functor.leftUnitor (𝟭 B₀)) eB.counitIso
    (BaseChange.transformCounitIso.leftCoherence F G eB)
      (BaseChange.transformCounitIso.rightCoherence F G eB)

/-- Common base change along an equivalence, with its inverse transformation and both comparison
isomorphisms retained as explicit data. -/
noncomputable def BaseChange.transformQuasiInverse
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    CatCospanTransform.QuasiInverse (postcompose.transform F G eB.functor) where
  inverse := BaseChange.inverseTransform F G eB
  unitIso := BaseChange.transformUnitIso F G eB
  counitIso := BaseChange.transformCounitIso F G eB

/-- Explicit quasi-inverse data for common base change on categorical pullbacks. -/
noncomputable def BaseChange.quasiInverse
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    Functor.QuasiInverse (postcompose F G eB.functor) :=
  (BaseChange.transformQuasiInverse F G eB).toMapQuasiInverse

/-- The inverse retained by `BaseChange.quasiInverse` is the explicit inverse base-change functor. -/
@[simp]
theorem BaseChange.quasiInverse.inverse
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.quasiInverse F G eB).inverse = BaseChange.inverse F G eB := sorry

/-- The categorical pullback is invariant under postcomposing both legs with an equivalence of the
common base. -/
noncomputable def BaseChange.equivalence (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    F ⊡ G ≌ (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor) :=
  (BaseChange.quasiInverse F G eB).adjointifyUnit

/-- The forward functor of base congruence is canonical base change.

Proof strategy: project the `functor` field of `BaseChange.equivalence`. -/
@[simp]
theorem BaseChange.equivalence.functor (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).functor = postcompose F G eB.functor := sorry

/-- The inverse functor of base congruence is the explicit inverse base-change functor. -/
@[simp]
theorem BaseChange.equivalence.inverse (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).inverse = BaseChange.inverse F G eB := sorry

/-- The counit of base congruence is the counit induced from the explicit inverse cospan
transformation. -/
@[simp]
theorem BaseChange.equivalence.counitIso (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).counitIso =
      (BaseChange.transformQuasiInverse F G eB).mapCounitIso := sorry

/-- The unit of base congruence is the canonical adjointification of the explicit unit and
counit induced from the inverse cospan transformation. -/
theorem BaseChange.equivalence.unitIso (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).unitIso =
      Equivalence.adjointifyη
        (BaseChange.transformQuasiInverse F G eB).mapUnitIso
          (BaseChange.transformQuasiInverse F G eB).mapCounitIso := sorry

/-- The unit of base congruence is the identity on the left endpoint. -/
@[simp]
theorem BaseChange.equivalence.unitIso.hom.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') (x : F ⊡ G) :
    ((BaseChange.equivalence F G eB).unitIso.hom.app x).fst = 𝟙 x.fst := sorry

/-- The unit of base congruence is the identity on the right endpoint. -/
@[simp]
theorem BaseChange.equivalence.unitIso.hom.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') (x : F ⊡ G) :
    ((BaseChange.equivalence F G eB).unitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- The inverse component of the base-congruence unit is the identity on the left endpoint. -/
@[simp]
theorem BaseChange.equivalence.unitIso.inv.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') (x : F ⊡ G) :
    ((BaseChange.equivalence F G eB).unitIso.inv.app x).fst = 𝟙 x.fst := sorry

/-- The inverse component of the base-congruence unit is the identity on the right endpoint. -/
@[simp]
theorem BaseChange.equivalence.unitIso.inv.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') (x : F ⊡ G) :
    ((BaseChange.equivalence F G eB).unitIso.inv.app x).snd = 𝟙 x.snd := sorry

/-- The counit of base congruence is the identity on the left endpoint. -/
@[simp]
theorem BaseChange.equivalence.counitIso.hom.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.equivalence F G eB).counitIso.hom.app x).fst = 𝟙 x.fst := sorry

/-- The counit of base congruence is the identity on the right endpoint. -/
@[simp]
theorem BaseChange.equivalence.counitIso.hom.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.equivalence F G eB).counitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- The inverse component of the base-congruence counit is the identity on the left endpoint. -/
@[simp]
theorem BaseChange.equivalence.counitIso.inv.app.fst
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.equivalence F G eB).counitIso.inv.app x).fst = 𝟙 x.fst := sorry

/-- The inverse component of the base-congruence counit is the identity on the right endpoint. -/
@[simp]
theorem BaseChange.equivalence.counitIso.inv.app.snd
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.equivalence F G eB).counitIso.inv.app x).snd = 𝟙 x.snd := sorry

/-- Forward base-change equivalence is compatible with the first projection. -/
noncomputable def BaseChange.equivalence.functorFstIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).functor ⋙
        π₁ (F ⋙ eB.functor) (G ⋙ eB.functor) ≅
      π₁ F G :=
  Functor.isoWhiskerRight
      (eqToIso (BaseChange.equivalence.functor F G eB))
      (π₁ (F ⋙ eB.functor) (G ⋙ eB.functor)) ≪≫
    postcomposeFstIso F G eB.functor

/-- The inverse base-change equivalence is compatible with the first projection. -/
noncomputable def BaseChange.equivalence.inverseFstIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).inverse ⋙ π₁ F G ≅
      π₁ (F ⋙ eB.functor) (G ⋙ eB.functor) :=
  Iso.inverseCompIso (BaseChange.equivalence.functorFstIso F G eB).symm

/-- Forward base-change equivalence is compatible with the second projection. -/
noncomputable def BaseChange.equivalence.functorSndIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).functor ⋙
        π₂ (F ⋙ eB.functor) (G ⋙ eB.functor) ≅
      π₂ F G :=
  Functor.isoWhiskerRight
      (eqToIso (BaseChange.equivalence.functor F G eB))
      (π₂ (F ⋙ eB.functor) (G ⋙ eB.functor)) ≪≫
    postcomposeSndIso F G eB.functor

/-- The inverse base-change equivalence is compatible with the second projection. -/
noncomputable def BaseChange.equivalence.inverseSndIso
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀') :
    (BaseChange.equivalence F G eB).inverse ⋙ π₂ F G ≅
      π₂ (F ⋙ eB.functor) (G ⋙ eB.functor) :=
  Iso.inverseCompIso (BaseChange.equivalence.functorSndIso F G eB).symm

end CatPullbackCongr

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback

end CategoryTheory
