/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
public import ReasLib.CategoryTheory.Functor.Equivalence
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.MapProperties

/-!
# Leg-isomorphism transport of categorical pullbacks

Transport along natural isomorphisms of the two cospan legs, including the induced equivalence and
projection comparisons.
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
/-- Transport along natural isomorphisms of both legs, expressed as a categorical cospan
transformation with identity endpoint and base functors. -/
def LegChange.transform {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    CatCospanTransform F G F' G' :=
  CatCospanTransform.ofIso
    (Functor.rightUnitor F ≪≫ eF ≪≫ (Functor.leftUnitor F').symm)
    (Functor.rightUnitor G ≪≫ eG ≪≫ (Functor.leftUnitor G').symm)

/-- Natural isomorphisms of both legs induce a functor `F ⊡ G ⥤ F' ⊡ G'`. -/
noncomputable def LegChange.map {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    F ⊡ G ⥤ F' ⊡ G' :=
  CategoricalPullback.map (LegChange.transform eF eG)

namespace Implementation

/-- The forward structural map of leg transport, computed from the explicit cospan map. -/
private theorem LegChange.map_obj_iso_hom
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    (x : F ⊡ G) :
    ((LegChange.map eF eG).obj x).iso.hom =
      eF.inv.app x.fst ≫ x.iso.hom ≫ eG.hom.app x.snd := by
  change 𝟙 _ ≫ ((𝟙 _ ≫ eF.inv.app x.fst) ≫ 𝟙 _) ≫
      𝟙 _ ≫ x.iso.hom ≫ 𝟙 _ ≫ (𝟙 _ ≫ eG.hom.app x.snd ≫ 𝟙 _) ≫ 𝟙 _ =
    eF.inv.app x.fst ≫ x.iso.hom ≫ eG.hom.app x.snd
  simp only [Category.id_comp, Category.comp_id]

/-- Transporting along a pair of leg isomorphisms and back restores the structural map. -/
private theorem LegChange.map_roundTrip_iso_hom
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    (x : F ⊡ G) :
    ((LegChange.map eF.symm eG.symm).obj ((LegChange.map eF eG).obj x)).iso.hom =
      x.iso.hom := by
  rw [LegChange.map_obj_iso_hom, LegChange.map_obj_iso_hom]
  change eF.hom.app x.fst ≫
      (eF.inv.app x.fst ≫ x.iso.hom ≫ eG.hom.app x.snd) ≫ eG.inv.app x.snd =
    x.iso.hom
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Category.comp_id]

end Implementation

namespace LegChange.map

/-- Transport along invertible changes of both cospan legs is an equivalence.

This owner-specialized instance exposes the generic
`CategoricalPullback.map.isEquivalence` result to typeclass search without unfolding the
convenience definition `LegChange.map`. Its inherited `Full`, `Faithful`, and `EssSurj` instances
therefore remain available at the same public owner. -/
instance isEquivalence {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.map eF eG).IsEquivalence := by
  let unit {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
      (eF : F ≅ F') (eG : G ≅ G') :
      𝟭 (F ⊡ G) ≅ LegChange.map eF eG ⋙ LegChange.map eF.symm eG.symm :=
    NatIso.ofComponents
      (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
        (by
          change F.map (𝟙 x.fst) ≫ _ = x.iso.hom ≫ G.map (𝟙 x.snd)
          rw [Functor.map_id, Functor.map_id]
          exact (Category.id_comp _).trans
            ((Implementation.LegChange.map_roundTrip_iso_hom eF eG x).trans
              (Category.comp_id _).symm)))
      (by
        intro x y f
        apply CategoricalPullback.hom_ext
        · change f.fst ≫ 𝟙 _ = 𝟙 _ ≫ f.fst
          simp only [Category.id_comp, Category.comp_id]
        · change f.snd ≫ 𝟙 _ = 𝟙 _ ≫ f.snd
          simp only [Category.id_comp, Category.comp_id])
  exact Functor.IsEquivalence.mk' (LegChange.map eF.symm eG.symm)
    (unit eF eG) (unit eF.symm eG.symm).symm

end LegChange.map

/-- Transporting the legs retains the left object.

Proof strategy: project the explicit object formula of `LegChange.map`. -/
@[simp]
theorem LegChange.map.obj.fst {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.map eF eG).obj x).fst = x.fst := rfl

/-- Transporting the legs retains the right object.

Proof strategy: project the explicit object formula of `LegChange.map`. -/
@[simp]
theorem LegChange.map.obj.snd {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.map eF eG).obj x).snd = x.snd := rfl

/-- Transporting the legs conjugates the structural isomorphism by the two given leg
isomorphisms.

Proof strategy: project the structural isomorphism of the explicit object formula of `LegChange.map`. -/
@[simp]
theorem LegChange.map.obj.iso {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.map eF eG).obj x).iso =
      (eF.app x.fst).symm ≪≫ x.iso ≪≫ eG.app x.snd := by
  apply Iso.ext
  exact Implementation.LegChange.map_obj_iso_hom eF eG x

/-- Transporting the legs retains the left component of a morphism.

Proof strategy: project the explicit morphism formula of `LegChange.map`. -/
@[simp]
theorem LegChange.map.hom.fst {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') {x y : F ⊡ G} (f : x ⟶ y) :
    ((LegChange.map eF eG).map f).fst = f.fst := rfl

/-- Transporting the legs retains the right component of a morphism.

Proof strategy: project the explicit morphism formula of `LegChange.map`. -/
@[simp]
theorem LegChange.map.hom.snd {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') {x y : F ⊡ G} (f : x ⟶ y) :
    ((LegChange.map eF eG).map f).snd = f.snd := rfl

namespace Implementation

/-- Coherence for the unit component of invariance under isomorphic legs. -/
private theorem LegChange.unitComponent_w
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    (x : F ⊡ G) :
    F.map (𝟙 x.fst) ≫
        ((LegChange.map eF eG ⋙ LegChange.map eF.symm eG.symm).obj x).iso.hom =
      x.iso.hom ≫ G.map (𝟙 x.snd) := by
  rw [Functor.map_id, Functor.map_id]
  exact (Category.id_comp _).trans
    ((LegChange.map_roundTrip_iso_hom eF eG x).trans (Category.comp_id _).symm)
/- Proof strategy: unfold both leg transports and cancel the adjacent components of `eF` and
`eG`; the remaining identity maps reduce to the original structural isomorphism. -/

/-- Objectwise unit isomorphism for invariance under isomorphic legs. -/
private noncomputable def LegChange.unitComponent
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    (x : F ⊡ G) :
    x ≅ (LegChange.map eF eG ⋙ LegChange.map eF.symm eG.symm).obj x :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    (LegChange.unitComponent_w eF eG x)

/-- Naturality of the unit components for invariance under isomorphic legs. -/
private theorem LegChange.unitNaturality
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    {x y : F ⊡ G} (f : x ⟶ y) :
    f ≫ (LegChange.unitComponent eF eG y).hom =
      (LegChange.unitComponent eF eG x).hom ≫
        (LegChange.map eF eG ⋙ LegChange.map eF.symm eG.symm).map f := by
  apply CategoricalPullback.hom_ext
  · change f.fst ≫ 𝟙 _ = 𝟙 _ ≫ f.fst
    simp only [Category.id_comp, Category.comp_id]
  · change f.snd ≫ 𝟙 _ = 𝟙 _ ≫ f.snd
    simp only [Category.id_comp, Category.comp_id]
/- Proof strategy: apply `CategoricalPullback.hom_ext`; both projections are identity whiskerings
of `f.fst` and `f.snd`. -/

/-- Unit natural isomorphism for invariance under isomorphic legs. -/
private noncomputable def LegChange.unitIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G') :
    𝟭 (F ⊡ G) ≅ LegChange.map eF eG ⋙ LegChange.map eF.symm eG.symm :=
  NatIso.ofComponents (LegChange.unitComponent eF eG)
    (LegChange.unitNaturality eF eG)

/-- Coherence for the counit component of invariance under isomorphic legs. -/
private theorem LegChange.counitComponent_w
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    (x : F' ⊡ G') :
    F'.map (𝟙 x.fst) ≫ x.iso.hom =
      ((LegChange.map eF.symm eG.symm ⋙ LegChange.map eF eG).obj x).iso.hom ≫
        G'.map (𝟙 x.snd) := by
  calc
    F'.map (𝟙 x.fst) ≫ x.iso.hom = x.iso.hom := by
      rw [Functor.map_id]
      exact Category.id_comp _
    _ = ((LegChange.map eF.symm eG.symm ⋙ LegChange.map eF eG).obj x).iso.hom :=
      (LegChange.map_roundTrip_iso_hom eF.symm eG.symm x).symm
    _ = _ := (Category.comp_id _).symm.trans
      (congrArg (fun f =>
        ((LegChange.map eF.symm eG.symm ⋙ LegChange.map eF eG).obj x).iso.hom ≫ f)
        (G'.map_id x.snd).symm)
/- Proof strategy: unfold both leg transports and cancel the adjacent components of `eF` and
`eG`; the remaining identity maps reduce to the target structural isomorphism. -/

/-- Objectwise counit isomorphism for invariance under isomorphic legs. -/
private noncomputable def LegChange.counitComponent
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    (x : F' ⊡ G') :
    (LegChange.map eF.symm eG.symm ⋙ LegChange.map eF eG).obj x ≅ x :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _)
    (LegChange.counitComponent_w eF eG x)

/-- Naturality of the counit components for invariance under isomorphic legs. -/
private theorem LegChange.counitNaturality
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G')
    {x y : F' ⊡ G'} (f : x ⟶ y) :
    (LegChange.map eF.symm eG.symm ⋙ LegChange.map eF eG).map f ≫
        (LegChange.counitComponent eF eG y).hom =
      (LegChange.counitComponent eF eG x).hom ≫ f := by
  apply CategoricalPullback.hom_ext
  · change f.fst ≫ 𝟙 _ = 𝟙 _ ≫ f.fst
    simp only [Category.id_comp, Category.comp_id]
  · change f.snd ≫ 𝟙 _ = 𝟙 _ ≫ f.snd
    simp only [Category.id_comp, Category.comp_id]
/- Proof strategy: apply `CategoricalPullback.hom_ext`; both projections are identity whiskerings
of `f.fst` and `f.snd`. -/

/-- Counit natural isomorphism for invariance under isomorphic legs. -/
private noncomputable def LegChange.counitIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀} (eF : F ≅ F') (eG : G ≅ G') :
    LegChange.map eF.symm eG.symm ⋙ LegChange.map eF eG ≅ 𝟭 (F' ⊡ G') :=
  NatIso.ofComponents (LegChange.counitComponent eF eG)
    (LegChange.counitNaturality eF eG)

end Implementation

/-- Explicit quasi-inverse data for transport along natural isomorphisms of both pullback
legs. -/
noncomputable def LegChange.quasiInverse
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    Functor.QuasiInverse (LegChange.map eF eG) where
  inverse := LegChange.map eF.symm eG.symm
  unitIso := Implementation.LegChange.unitIso eF eG
  counitIso := Implementation.LegChange.counitIso eF eG

/-- The inverse retained by leg-transport quasi-inverse data transports along the inverse
isomorphisms. -/
@[simp]
theorem LegChange.quasiInverse.inverse
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.quasiInverse eF eG).inverse =
      LegChange.map eF.symm eG.symm := rfl

/-- The categorical pullback is invariant under natural isomorphisms of the two legs. -/
noncomputable def LegChange.equivalence {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') : F ⊡ G ≌ F' ⊡ G' :=
  (LegChange.quasiInverse eF eG).adjointifyUnit

/-- The forward functor of leg congruence transports both structural legs.

Proof strategy: project the `functor` field of `LegChange.equivalence`. -/
@[simp]
theorem LegChange.equivalence.functor {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).functor = LegChange.map eF eG := rfl

/-- The inverse functor of leg congruence transports along the inverse leg isomorphisms.

Proof strategy: project the `inverse` field of `LegChange.equivalence`. -/
@[simp]
theorem LegChange.equivalence.inverse {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).inverse = LegChange.map eF.symm eG.symm := rfl

/-- The counit of leg congruence is the explicitly specified leg-transport counit. -/
@[simp]
theorem LegChange.equivalence.counitIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).counitIso =
      (LegChange.quasiInverse eF eG).counitIso := rfl

/-- The unit of leg congruence is the canonical adjointification of the specified
leg-transport unit against its counit. -/
theorem LegChange.equivalence.unitIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).unitIso =
      Equivalence.adjointifyη
        (LegChange.quasiInverse eF eG).unitIso
          (LegChange.quasiInverse eF eG).counitIso := rfl

/-- The unit of leg congruence is the identity on the left component.

Proof strategy: project the explicit unit component through `CategoricalPullback.mkIso`. -/
@[simp]
theorem LegChange.equivalence.unitIso.hom.app.fst
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.equivalence eF eG).unitIso.hom.app x).fst = 𝟙 x.fst := by
  have h := congrArg CategoricalPullback.Hom.fst
    ((LegChange.equivalence eF eG).functor_unitIso_comp x)
  change ((LegChange.equivalence eF eG).unitIso.hom.app x).fst ≫ 𝟙 x.fst =
    𝟙 x.fst at h
  exact (Category.comp_id _).symm.trans h

/-- The unit of leg congruence is the identity on the right component.

Proof strategy: project the explicit unit component through `CategoricalPullback.mkIso`. -/
@[simp]
theorem LegChange.equivalence.unitIso.hom.app.snd
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.equivalence eF eG).unitIso.hom.app x).snd = 𝟙 x.snd := by
  have h := congrArg CategoricalPullback.Hom.snd
    ((LegChange.equivalence eF eG).functor_unitIso_comp x)
  change ((LegChange.equivalence eF eG).unitIso.hom.app x).snd ≫ 𝟙 x.snd =
    𝟙 x.snd at h
  exact (Category.comp_id _).symm.trans h

/-- The inverse component of the leg-congruence unit is the identity on the left endpoint. -/
@[simp]
theorem LegChange.equivalence.unitIso.inv.app.fst
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.equivalence eF eG).unitIso.inv.app x).fst = 𝟙 x.fst := by
  have h := congrArg CategoricalPullback.Hom.fst
    ((LegChange.equivalence eF eG).unitIso.hom_inv_id_app x)
  change ((LegChange.equivalence eF eG).unitIso.hom.app x).fst ≫
    ((LegChange.equivalence eF eG).unitIso.inv.app x).fst = 𝟙 x.fst at h
  rw [LegChange.equivalence.unitIso.hom.app.fst] at h
  exact (Category.id_comp _).symm.trans h

/-- The inverse component of the leg-congruence unit is the identity on the right endpoint. -/
@[simp]
theorem LegChange.equivalence.unitIso.inv.app.snd
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F ⊡ G) :
    ((LegChange.equivalence eF eG).unitIso.inv.app x).snd = 𝟙 x.snd := by
  have h := congrArg CategoricalPullback.Hom.snd
    ((LegChange.equivalence eF eG).unitIso.hom_inv_id_app x)
  change ((LegChange.equivalence eF eG).unitIso.hom.app x).snd ≫
    ((LegChange.equivalence eF eG).unitIso.inv.app x).snd = 𝟙 x.snd at h
  rw [LegChange.equivalence.unitIso.hom.app.snd] at h
  exact (Category.id_comp _).symm.trans h

/-- The counit of leg congruence is the identity on the left component.

Proof strategy: project the explicit counit component through `CategoricalPullback.mkIso`. -/
@[simp]
theorem LegChange.equivalence.counitIso.hom.app.fst
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F' ⊡ G') :
    ((LegChange.equivalence eF eG).counitIso.hom.app x).fst = 𝟙 x.fst := rfl

/-- The counit of leg congruence is the identity on the right component.

Proof strategy: project the explicit counit component through `CategoricalPullback.mkIso`. -/
@[simp]
theorem LegChange.equivalence.counitIso.hom.app.snd
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F' ⊡ G') :
    ((LegChange.equivalence eF eG).counitIso.hom.app x).snd = 𝟙 x.snd := rfl

/-- The inverse component of the leg-congruence counit is the identity on the left endpoint. -/
@[simp]
theorem LegChange.equivalence.counitIso.inv.app.fst
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F' ⊡ G') :
    ((LegChange.equivalence eF eG).counitIso.inv.app x).fst = 𝟙 x.fst := rfl

/-- The inverse component of the leg-congruence counit is the identity on the right endpoint. -/
@[simp]
theorem LegChange.equivalence.counitIso.inv.app.snd
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') (x : F' ⊡ G') :
    ((LegChange.equivalence eF eG).counitIso.inv.app x).snd = 𝟙 x.snd := rfl

/-- Forward leg-change equivalence is compatible with the first projection. -/
noncomputable def LegChange.equivalence.functorFstIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).functor ⋙ π₁ F' G' ≅
      π₁ F G :=
  Iso.refl _

/-- The inverse leg-change equivalence is compatible with the first projection. -/
noncomputable def LegChange.equivalence.inverseFstIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).inverse ⋙ π₁ F G ≅
      π₁ F' G' :=
  Iso.inverseCompIso (LegChange.equivalence.functorFstIso eF eG).symm

/-- Forward leg-change equivalence is compatible with the second projection. -/
noncomputable def LegChange.equivalence.functorSndIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).functor ⋙ π₂ F' G' ≅
      π₂ F G :=
  Iso.refl _

/-- The inverse leg-change equivalence is compatible with the second projection. -/
noncomputable def LegChange.equivalence.inverseSndIso
    {F F' : A₀ ⥤ D₀} {G G' : B₀ ⥤ D₀}
    (eF : F ≅ F') (eG : G ≅ G') :
    (LegChange.equivalence eF eG).inverse ⋙ π₂ F G ≅
      π₂ F' G' :=
  Iso.inverseCompIso (LegChange.equivalence.functorSndIso eF eG).symm

end CatPullbackCongr

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback

end CategoryTheory
