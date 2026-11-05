/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# Projective-space section data

This file defines invertible module sheaves equipped with a finite generating family of global
sections, their isomorphism classes, and their contravariant pullback functor on schemes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpaceDatum

/-- The free module sheaf whose basis indexes a family of `n + 1` sections. -/
abbrev sectionFamilySource (X : Scheme.{u}) (n : ℕ) : X.Modules :=
  (SheafOfModules.free (ULift.{u} (Fin (n + 1))) : X.Modules)

/-- The evaluation morphism from the free module sheaf determined by a section family. -/
def sectionFamilyHom {X : Scheme.{u}} (ℒ : X.Modules) (n : ℕ)
    (s : Fin (n + 1) → ℒ.sections) : sectionFamilySource X n ⟶ ℒ :=
  ℒ.freeHomEquiv.symm (fun i : ULift.{u} (Fin (n + 1)) ↦ s i.down)

end ProjectiveSpaceDatum

/-- An invertible module sheaf on a scheme equipped with `n + 1` generating global sections. -/
structure ProjectiveSpaceDatum (n : ℕ) (Y : Scheme.{u}) where
  /-- The invertible module sheaf. -/
  lineBundle : Y.Modules
  /-- Invertibility of the module sheaf. -/
  invertible_lineBundle : Scheme.Modules.Invertible lineBundle
  /-- The indexed family of global sections. -/
  sections : Fin (n + 1) → lineBundle.sections
  /-- The section family generates the module sheaf. -/
  generates : Epi (ProjectiveSpaceDatum.sectionFamilyHom lineBundle n sections)

namespace ProjectiveSpaceDatum

/-- Construct projective-space data from an invertible module and a generating section family. -/
def ofSections {n : ℕ} {Y : Scheme.{u}} (lineBundle : Y.Modules)
    (invertible_lineBundle : Scheme.Modules.Invertible lineBundle)
    (sections : Fin (n + 1) → lineBundle.sections)
    (generates : Epi (sectionFamilyHom lineBundle n sections)) :
    ProjectiveSpaceDatum n Y where
  lineBundle := lineBundle
  invertible_lineBundle := invertible_lineBundle
  sections := sections
  generates := generates

/-- The invertibility and generation conditions carried by projective-space data hold together. -/
theorem conditions_spec {n : ℕ} {Y : Scheme.{u}} (τ : ProjectiveSpaceDatum n Y) :
    Scheme.Modules.Invertible τ.lineBundle ∧
      Epi (sectionFamilyHom τ.lineBundle n τ.sections) :=
  ⟨τ.invertible_lineBundle, τ.generates⟩

/-- Two projective-space data are equivalent when an isomorphism of their module sheaves
carries every section of the first family to the corresponding section of the second. -/
def Equivalent {n : ℕ} {Y : Scheme.{u}} (τ τ' : ProjectiveSpaceDatum n Y) : Prop :=
  ∃ β : τ.lineBundle ≅ τ'.lineBundle,
    ∀ i : Fin (n + 1),
      SheafOfModules.sectionsMap β.hom (τ.sections i) = τ'.sections i

/-- Equivalence of projective-space data is reflexive. -/
theorem equivalent_refl {n : ℕ} {Y : Scheme.{u}} (τ : ProjectiveSpaceDatum n Y) :
    Equivalent τ τ :=
  ⟨Iso.refl _, fun _ ↦ rfl⟩

/-- Equivalence of projective-space data is symmetric. -/
theorem equivalent_symm {n : ℕ} {Y : Scheme.{u}} {τ τ' : ProjectiveSpaceDatum n Y} :
    Equivalent τ τ' → Equivalent τ' τ := by
  rintro ⟨β, hβ⟩
  refine ⟨β.symm, fun i ↦ ?_⟩
  change SheafOfModules.sectionsMap β.inv (τ'.sections i) = τ.sections i
  rw [← hβ i, ← SheafOfModules.sectionsMap_comp]
  exact congrArg (fun p : τ.lineBundle ⟶ τ.lineBundle ↦
    SheafOfModules.sectionsMap p (τ.sections i)) β.hom_inv_id

/-- Equivalence of projective-space data is transitive. -/
theorem equivalent_trans {n : ℕ} {Y : Scheme.{u}}
    {τ τ' τ'' : ProjectiveSpaceDatum n Y} :
    Equivalent τ τ' → Equivalent τ' τ'' → Equivalent τ τ'' := by
  rintro ⟨β, hβ⟩ ⟨γ, hγ⟩
  refine ⟨β ≪≫ γ, fun i ↦ ?_⟩
  change SheafOfModules.sectionsMap γ.hom
    (SheafOfModules.sectionsMap β.hom (τ.sections i)) = τ''.sections i
  rw [hβ i, hγ i]

/-- The setoid of projective-space data under section-preserving module isomorphisms. -/
def setoid (n : ℕ) (Y : Scheme.{u}) : Setoid (ProjectiveSpaceDatum n Y) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

private theorem sections_ext_top {X : Scheme.{u}} {M : X.Modules} {s t : M.sections}
    (h : s.1 (Opposite.op ⊤) = t.1 (Opposite.op ⊤)) : s = t := by
  apply PresheafOfModules.sections_ext
  intro U
  exact (s.2 (RingedSpace.topOpenRestriction U)).symm.trans
    ((congrArg (fun x ↦ M.val.map (RingedSpace.topOpenRestriction U) x) h).trans
      (t.2 (RingedSpace.topOpenRestriction U)))

private theorem sectionsPullback_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : M.sections) :
    (Scheme.Modules.sectionsPullback f M s).1 (Opposite.op ⊤) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
        (Opposite.op ⊤) (s.1 (Opposite.op ⊤)) := by
  change (((Scheme.Modules.pullback f).obj M).presheaf.map (𝟙 _)) _ = _
  simp
  rfl

private theorem sectionsPullback_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (p : M ⟶ N) (s : M.sections) :
    SheafOfModules.sectionsMap ((Scheme.Modules.pullback f).map p)
        (Scheme.Modules.sectionsPullback f M s) =
      Scheme.Modules.sectionsPullback f N (SheafOfModules.sectionsMap p s) := by
  apply sections_ext_top
  change ((Scheme.Modules.pullback f).map p).val.app _
      ((Scheme.Modules.sectionsPullback f M s).1 _) =
    (Scheme.Modules.sectionsPullback f N (SheafOfModules.sectionsMap p s)).1 _
  rw [sectionsPullback_top, sectionsPullback_top]
  exact congrArg (fun k : M ⟶ (Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj N) ↦ k.val.app (Opposite.op ⊤) (s.1 _))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality p).symm

set_option backward.isDefEq.respectTransparency false in
/-- Pullback preserves generation by a finite family of global sections. -/
theorem pullback_generates {n : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (τ : ProjectiveSpaceDatum n Y) :
    Epi (sectionFamilyHom ((Scheme.Modules.pullback f).obj τ.lineBundle) n
      (fun i ↦ Scheme.Modules.sectionsPullback f τ.lineBundle (τ.sections i))) := by
  letI : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat (TopologicalSpace.Opens.map f.base)
  let I := ULift.{u} (Fin (n + 1))
  let e : SheafOfModules.free (R := X.ringCatSheaf) I ≅
      (Scheme.Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) :=
    SheafOfModules.mapFreeIso (SheafOfModules.pullback f.toRingCatSheafHom) I
      (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).symm
  letI := τ.generates
  have h : e.hom ≫ (Scheme.Modules.pullback f).map
      (sectionFamilyHom τ.lineBundle n τ.sections) =
      sectionFamilyHom ((Scheme.Modules.pullback f).obj τ.lineBundle) n
        (fun i ↦ Scheme.Modules.sectionsPullback f τ.lineBundle (τ.sections i)) := by
    apply ((Scheme.Modules.pullback f).obj τ.lineBundle).freeHomEquiv.injective
    funext i
    simp only [sectionFamilyHom]
    change ((Scheme.Modules.pullback f).obj τ.lineBundle).unitHomEquiv
      (SheafOfModules.ιFree i ≫ e.hom ≫ (SheafOfModules.pullback f.toRingCatSheafHom).map
        (τ.lineBundle.freeHomEquiv.symm (fun j : I ↦ τ.sections j.down))) = _
    rw [SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← Functor.map_comp,
      ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [Equiv.apply_symm_apply]
    exact (Scheme.Modules.sectionsPullback_eq_unitHomEquiv f τ.lineBundle (τ.sections i.down)).symm.trans
      (congrFun (((Scheme.Modules.pullback f).obj τ.lineBundle).freeHomEquiv.apply_symm_apply
        (fun j : I ↦ Scheme.Modules.sectionsPullback f τ.lineBundle (τ.sections j.down))) i).symm
  rw [← h]
  infer_instance

/-- Pull back an invertible module sheaf together with its generating sections. -/
noncomputable def pullback {n : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (τ : ProjectiveSpaceDatum n Y) : ProjectiveSpaceDatum n X :=
  ofSections ((Scheme.Modules.pullback f).obj τ.lineBundle)
    (Scheme.Modules.Invertible.pullback f τ.invertible_lineBundle)
    (fun i ↦ Scheme.Modules.sectionsPullback f τ.lineBundle (τ.sections i))
    (pullback_generates f τ)

/-- Pullback carries equivalent projective-space data to equivalent data. -/
theorem pullback_equivalent {n : ℕ} {X Y : Scheme.{u}} (f : X ⟶ Y)
    {τ τ' : ProjectiveSpaceDatum n Y} :
    Equivalent τ τ' → Equivalent (pullback f τ) (pullback f τ') := by
  rintro ⟨β, hβ⟩
  refine ⟨(Scheme.Modules.pullback f).mapIso β, fun i ↦ ?_⟩
  change SheafOfModules.sectionsMap ((Scheme.Modules.pullback f).map β.hom)
      (Scheme.Modules.sectionsPullback f τ.lineBundle (τ.sections i)) =
    Scheme.Modules.sectionsPullback f τ'.lineBundle (τ'.sections i)
  rw [sectionsPullback_naturality, hβ i]

/-- Pullback along an identity morphism is equivalent to the original data. -/
theorem pullback_id_equivalent {n : ℕ} {Y : Scheme.{u}} (τ : ProjectiveSpaceDatum n Y) :
    Equivalent (pullback (𝟙 Y) τ) τ := by
  refine ⟨(Scheme.Modules.pullbackId Y).app τ.lineBundle, fun i ↦ ?_⟩
  apply sections_ext_top
  change ((Scheme.Modules.pullbackId Y).hom.app τ.lineBundle).val.app _
    ((Scheme.Modules.sectionsPullback (𝟙 Y) τ.lineBundle (τ.sections i)).1 _) =
      (τ.sections i).1 _
  rw [sectionsPullback_top]
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Y))
    (Scheme.Modules.pullbackId Y).hom τ.lineBundle
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun k : τ.lineBundle ⟶ (Scheme.Modules.pushforward (𝟙 Y)).obj τ.lineBundle ↦
    k.val.app (Opposite.op ⊤) ((τ.sections i).1 _)) h).symm

/-- Pullback along a composite is equivalent to iterated pullback. -/
theorem pullback_comp_equivalent {n : ℕ} {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ X) (τ : ProjectiveSpaceDatum n Y) :
    Equivalent (pullback (g ≫ f) τ) (pullback g (pullback f τ)) := by
  refine ⟨((Scheme.Modules.pullbackComp g f).app τ.lineBundle).symm, fun i ↦ ?_⟩
  apply sections_ext_top
  change ((Scheme.Modules.pullbackComp g f).inv.app τ.lineBundle).val.app _
      ((Scheme.Modules.sectionsPullback (g ≫ f) τ.lineBundle (τ.sections i)).1 _) =
    (Scheme.Modules.sectionsPullback g ((Scheme.Modules.pullback f).obj τ.lineBundle)
      (Scheme.Modules.sectionsPullback f τ.lineBundle (τ.sections i))).1 _
  rw [sectionsPullback_top, sectionsPullback_top, sectionsPullback_top]
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f))
    (Scheme.Modules.pullbackComp g f).inv τ.lineBundle
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (congrArg (fun k : τ.lineBundle ⟶ (Scheme.Modules.pushforward (g ≫ f)).obj
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj τ.lineBundle)) ↦
    k.val.app (Opposite.op ⊤) ((τ.sections i).1 _)) h).symm

end ProjectiveSpaceDatum

/-- Isomorphism classes of invertible module sheaves with `n + 1` generating sections. -/
abbrev ProjectiveSpaceDatumClass (n : ℕ) (Y : Scheme.{u}) : Type (u + 1) :=
  _root_.Quotient (ProjectiveSpaceDatum.setoid n Y)

namespace ProjectiveSpaceDatumClass

/-- Pullback of module sheaves and sections induces a map on projective-space datum classes. -/
def map (n : ℕ) {S T : Scheme.{u}ᵒᵖ} (f : S ⟶ T) :
    ProjectiveSpaceDatumClass n S.unop ⟶ ProjectiveSpaceDatumClass n T.unop :=
  TypeCat.ofHom fun τ ↦ _root_.Quotient.map
    (ProjectiveSpaceDatum.pullback f.unop)
    (fun {_ _} h ↦ ProjectiveSpaceDatum.pullback_equivalent f.unop h) τ

/-- Pullback along an identity induces the identity map on datum classes. -/
theorem map_id (n : ℕ) (S : Scheme.{u}ᵒᵖ) :
    map n (𝟙 S) = 𝟙 (ProjectiveSpaceDatumClass n S.unop) := by
  ext τ
  refine _root_.Quotient.inductionOn τ ?_
  intro τ
  exact _root_.Quotient.sound (ProjectiveSpaceDatum.pullback_id_equivalent τ)

/-- Pullback along a composite induces the composite map on datum classes. -/
theorem map_comp (n : ℕ) {S T U : Scheme.{u}ᵒᵖ} (f : S ⟶ T) (g : T ⟶ U) :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext τ
  refine _root_.Quotient.inductionOn τ ?_
  intro τ
  exact _root_.Quotient.sound
    (ProjectiveSpaceDatum.pullback_comp_equivalent f.unop g.unop τ)

/-- The contravariant functor of invertible module sheaves with `n + 1` generating sections. -/
def functor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj S := ProjectiveSpaceDatumClass n S.unop
  map f := map n f
  map_id S := map_id n S
  map_comp f g := map_comp n f g

/-- The value of the projective-space datum functor is the corresponding quotient of data. -/
theorem functor_obj (n : ℕ) (S : Scheme.{u}ᵒᵖ) :
    (functor n).obj S = ProjectiveSpaceDatumClass n S.unop := rfl

end ProjectiveSpaceDatumClass

end AlgebraicGeometry
