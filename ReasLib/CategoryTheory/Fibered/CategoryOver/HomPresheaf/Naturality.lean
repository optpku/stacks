/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
import ReasLib.CategoryTheory.Fibered.FiberwiseEquivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of fiberwise Hom-presheaf maps

This file gives the `2`-cell, endpoint, owner-isomorphism, and equivalence API
for `FiberedCategoryOver.Hom.presheafHomMap`.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

namespace FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem presheafHomMap_conjugation
    {A B D E : Type uS} [Category.{vS} A] [Category.{vS} B]
    [Category.{vS} D] [Category.{vS} E]
    {R : A ⥤ B} {S : D ⥤ E} {H : B ⥤ E} {K : A ⥤ D}
    (e : R ⋙ H ≅ K ⋙ S) {x₁ x₂ y₁ y₂ : A}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (δ : R.obj x₁ ⟶ R.obj y₁) :
    e.inv.app x₂ ≫ H.map (R.map ex.inv ≫ δ ≫ R.map ey.hom) ≫ e.hom.app y₂ =
      S.map (K.map ex.inv) ≫ (e.inv.app x₁ ≫ H.map δ ≫ e.hom.app y₁) ≫
        S.map (K.map ey.hom) := by
  have hx : e.inv.app x₂ ≫ H.map (R.map ex.inv) =
      S.map (K.map ex.inv) ≫ e.inv.app x₁ := (e.inv.naturality ex.inv).symm
  have hy : H.map (R.map ey.hom) ≫ e.hom.app y₂ =
      e.hom.app y₁ ≫ S.map (K.map ey.hom) := e.hom.naturality ey.hom
  simp only [Functor.map_comp]
  calc
    _ = (e.inv.app x₂ ≫ H.map (R.map ex.inv)) ≫ H.map δ ≫
        (H.map (R.map ey.hom) ≫ e.hom.app y₂) := by simp only [Category.assoc]
    _ = (S.map (K.map ex.inv) ≫ e.inv.app x₁) ≫ H.map δ ≫
        (e.hom.app y₁ ≫ S.map (K.map ey.hom)) := by rw [hx, hy]
    _ = _ := by simp only [Category.assoc]

private theorem presheafHomMap_intertwine {E : Type uS} [Category.{vS} E]
    {a b c d a' b' c' d' : E}
    (ex : a ≅ b) (ey : c ≅ d) (ex' : a' ≅ b') (ey' : c' ≅ d')
    {f : a ⟶ c} {g : a' ⟶ c'} {tx : a ⟶ a'} {ty : c ⟶ c'}
    {p : b ⟶ b'} {q : d ⟶ d'}
    (hf : f ≫ ty = tx ≫ g)
    (hx : tx ≫ ex'.hom = ex.hom ≫ p)
    (hy : ty ≫ ey'.hom = ey.hom ≫ q) :
    (ex.inv ≫ f ≫ ey.hom) ≫ q = p ≫ (ex'.inv ≫ g ≫ ey'.hom) := by
  have hleft : ex.inv ≫ tx = p ≫ ex'.inv := by
    apply (cancel_mono ex'.hom).1
    rw [Category.assoc, hx]
    simp
  calc
    _ = ex.inv ≫ (f ≫ ty) ≫ ey'.hom := by simp only [Category.assoc, hy]
    _ = (ex.inv ≫ tx) ≫ g ≫ ey'.hom := by rw [hf]; simp [Category.assoc]
    _ = _ := by rw [hleft]; simp [Category.assoc]


/-- Hom-presheaf maps commute with a `2`-morphism between their owning
morphisms, acting at both endpoints in the target fiber. -/
@[stacks 042V "naturality of fixed-universe Hom-presheaf maps"]
theorem presheafHomMap.natural
    {F G : X ⟶ Y} (τ : F ⟶ G) {U : C} (x y : X.p.Fiber U) :
    presheafHomMap F x y ≫
        Pseudofunctor.PresheafHom.Postcomp.map
          (Functor.fiberPseudofunctor Y.p)
          ((FiberedCategoryOver.fiberNatTrans τ U).app y) =
      presheafHomMap G x y ≫
        Pseudofunctor.PresheafHom.Precomp.map
          (Functor.fiberPseudofunctor Y.p)
          ((FiberedCategoryOver.fiberNatTrans τ U).app x) := by
  ext W δ
  let R := Functor.Chosen.reindex X.p W.unop.hom
  let S := Functor.Chosen.reindex Y.p W.unop.hom
  let eF := Reindex.pseudonaturalityIso F W.unop.hom
  let eG := Reindex.pseudonaturalityIso G W.unop.hom
  have h (z : X.p.Fiber U) :
      (fiberNatTrans τ W.unop.left).app (R.obj z) ≫ eG.hom.app z =
        eF.hom.app z ≫ S.map ((fiberNatTrans τ U).app z) :=
    congrArg (fun η => η.toNatTrans.app z)
      ((strongTrans₂ τ).naturality W.unop.hom.op.toLoc)
  exact presheafHomMap_intertwine (eF.app x) (eF.app y) (eG.app x) (eG.app y)
    ((fiberNatTrans τ W.unop.left).naturality δ) (h x) (h y)


/-- The canonical Hom-presheaf map is natural in isomorphisms of both
endpoint objects. -/
@[stacks 042V "endpoint naturality of Hom-presheaf maps"]
theorem presheafHomMap.endpoints.iso
    (F : X ⟶ Y) {U : C} {x₁ x₂ y₁ y₂ : X.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) :
    (Pseudofunctor.PresheafHom.Congr.iso
        (Functor.fiberPseudofunctor X.p) ex ey).hom ≫
        presheafHomMap F x₂ y₂ =
      presheafHomMap F x₁ y₁ ≫
        (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctor F U).mapIso ex) ((fiberFunctor F U).mapIso ey)).hom := by
  ext W δ
  exact presheafHomMap_conjugation
    (Reindex.pseudonaturalityIso F W.unop.hom) ex ey δ

/-- Pointwise form of `presheafHomMap.endpoints.iso`. -/
@[stacks 042V "pointwise endpoint naturality of Hom-presheaf maps"]
theorem presheafHomMap.endpoints.iso.app
    (F : X ⟶ Y) {U : C} {x₁ x₂ y₁ y₂ : X.p.Fiber U}
    (ex : x₁ ≅ x₂) (ey : y₁ ≅ y₂) (W : (Over U)ᵒᵖ)
    (f : ((Functor.fiberPseudofunctor X.p).presheafHom x₁ y₁).obj W) :
    (presheafHomMap F x₂ y₂).app W
        ((Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor X.p) ex ey).hom.app W f) =
      (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctor F U).mapIso ex) ((fiberFunctor F U).mapIso ey)).hom.app W
        ((presheafHomMap F x₁ y₁).app W f) := by
  exact congrArg (fun η => η.app W f) (presheafHomMap.endpoints.iso F ex ey)

/-- Hom-presheaf maps attached to isomorphic morphisms of fibred categories
differ by the induced endpoint conjugation in the target fiber. -/
@[stacks 02ZA "invariance of Hom-presheaf maps under isomorphic owners"]
theorem presheafHomMap.ownerIso
    {F G : X ⟶ Y} (e : F ≅ G) {U : C} (x y : X.p.Fiber U) :
    presheafHomMap F x y ≫
        (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctorIso e U).app x) ((fiberFunctorIso e U).app y)).hom =
      presheafHomMap G x y := by
  ext W f
  let S := Functor.Chosen.reindex Y.p W.unop.hom
  let a : S.obj ((fiberFunctor F U).obj x) ⟶ S.obj ((fiberFunctor F U).obj y) :=
    (presheafHomMap F x y).app W f
  let b : S.obj ((fiberFunctor G U).obj x) ⟶ S.obj ((fiberFunctor G U).obj y) :=
    (presheafHomMap G x y).app W f
  have h := congrArg (fun η => η.app W f) (presheafHomMap.natural e.hom x y)
  change a ≫
      S.map ((fiberFunctorIso e U).hom.app y) =
    S.map ((fiberFunctorIso e U).hom.app x) ≫
      b at h
  change S.map ((fiberFunctorIso e U).inv.app x) ≫
      (a ≫
        S.map ((fiberFunctorIso e U).hom.app y)) =
    b
  rw [h, ← S.map_comp_assoc, ← NatTrans.comp_app,
    (fiberFunctorIso e U).inv_hom_id, NatTrans.id_app, S.map_id, Category.id_comp]

/-- Pointwise form of `presheafHomMap.ownerIso`. -/
@[stacks 02ZA "pointwise owner-isomorphism invariance of Hom-presheaf maps"]
theorem presheafHomMap.ownerIso.app
    {F G : X ⟶ Y} (e : F ≅ G) {U : C} (x y : X.p.Fiber U)
    (W : (Over U)ᵒᵖ)
    (f : ((Functor.fiberPseudofunctor X.p).presheafHom x y).obj W) :
    (presheafHomMap G x y).app W f =
      (Pseudofunctor.PresheafHom.Congr.iso
          (Functor.fiberPseudofunctor Y.p)
          ((fiberFunctorIso e U).app x) ((fiberFunctorIso e U).app y)).hom.app W
        ((presheafHomMap F x y).app W f) := by
  exact (congrArg (fun η => η.app W f) (presheafHomMap.ownerIso e x y)).symm

/-- Any isomorphism-invariant morphism property holds for the Hom-presheaf
maps of two isomorphic morphisms of fibred categories simultaneously. -/
@[stacks 02ZA "property invariance for isomorphic Hom-presheaf owners"]
theorem presheafHomMap.ownerIso.mem_iff
    {U : C} (P : MorphismProperty ((Over U)ᵒᵖ ⥤ Type vS)) [P.RespectsIso]
    {F G : X ⟶ Y} (e : F ≅ G) (x y : X.p.Fiber U) :
    P (presheafHomMap F x y) ↔ P (presheafHomMap G x y) := by
  rw [← presheafHomMap.ownerIso e x y]
  exact (P.cancel_right_of_respectsIso _ _).symm

/-- A morphism of fibred categories is fully faithful exactly when all its
canonical fiberwise Hom-presheaf maps are isomorphisms. -/
@[stacks 04WQ "full faithfulness via fixed-universe Hom-presheaf maps"]
theorem presheafHomMap.fullyFaithful_iff_isIso (F : X ⟶ Y) :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ {U : C} (x y : X.p.Fiber U), IsIso (presheafHomMap F x y) := by
  rw [FiberedCategoryOver.fullyFaithful_iff_fiberwise]
  constructor
  · intro h U x y
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro W
    apply (CategoryTheory.isIso_iff_bijective _).2
    obtain ⟨hW⟩ := h W.unop.left
    let e := Reindex.pseudonaturalityIso F W.unop.hom
    exact (Iso.homCongr (e.app x) (e.app y)).bijective.comp
      (hW.map_bijective _ _)
  · intro h U
    apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).2
    intro x y
    haveI := h x y
    have hbij := (CategoryTheory.isIso_iff_bijective
      ((presheafHomMap F x y).app (Opposite.op (Over.mk (𝟙 U))))).1 (by infer_instance)
    constructor
    · intro f g hfg
      apply (Functor.fiberPseudofunctor X.p).presheafHomObjHomEquiv.injective
      apply hbij.injective
      rw [presheafHomMap.app.identity, presheafHomMap.app.identity, hfg]
    · intro g
      obtain ⟨f, hf⟩ := hbij.surjective
        ((Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv g)
      obtain ⟨f, rfl⟩ := (Functor.fiberPseudofunctor X.p).presheafHomObjHomEquiv.surjective f
      refine ⟨f, (Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv.injective ?_⟩
      rwa [presheafHomMap.app.identity] at hf

/-- An equivalence over the base induces isomorphisms on all canonical
fiberwise Hom-presheaf maps. -/
@[stacks 02ZA "fixed-universe Hom-presheaf invariance under equivalence"]
theorem presheafHomMap.isIso_of_isEquivalence
    (F : X ⟶ Y) (hF : (toBasedFunctor F).IsEquivalence)
    {U : C} (x y : X.p.Fiber U) :
    IsIso (presheafHomMap F x y) := by
  obtain ⟨e⟩ := hF.nonempty
  haveI : (toFunctor F).IsEquivalence :=
    Functor.IsEquivalence.mk' e.inverse.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso e.unitIso)
      ((BasedNatTrans.forgetful _ _).mapIso e.counitIso)
  exact (presheafHomMap.fullyFaithful_iff_isIso F).1
    ⟨Functor.FullyFaithful.ofFullyFaithful _⟩ x y

/-- The canonical Hom-presheaf map of an equivalence over the base is
automatically available to typeclass search as an isomorphism. -/
@[stacks 02ZA "instance for equivalence Hom-presheaf maps"]
instance presheafHomMap.isIso
    (F : X ⟶ Y) [(toBasedFunctor F).IsEquivalence]
    {U : C} (x y : X.p.Fiber U) :
    IsIso (presheafHomMap F x y) := by
  exact presheafHomMap.isIso_of_isEquivalence F inferInstance x y

end FiberedCategoryOver.Hom

end CategoryTheory
