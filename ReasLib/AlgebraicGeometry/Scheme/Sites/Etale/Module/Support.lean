/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Module.Support

variable {X : Scheme.{u}}

/-- Sections over an étale object whose restriction to the inverse-image complement
of the support vanishes. -/
def sections (Z : Closeds X) (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X))
    (U : X.Etale) : Submodule ((AssociatedModule.smallStructureSheaf .etale X).obj.obj (op U))
      (F.val.obj (op U)) :=
  let W : U.left.Opens := U.hom ⁻¹ᵁ Z.compl
  LinearMap.ker (F.val.restrictₛₗ
    (MorphismProperty.Over.homMk W.ι : Scheme.Etale.mk (W.ι ≫ U.hom) ⟶ U).op)

/-- Membership in the supported section submodule is vanishing on the
inverse-image open complement. -/
theorem mem_sections_iff (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X))
    (U : X.Etale) (s : F.val.obj (op U)) :
    s ∈ sections Z F U ↔
      let W : U.left.Opens := U.hom ⁻¹ᵁ Z.compl
      F.val.map (MorphismProperty.Over.homMk W.ι :
        Scheme.Etale.mk (W.ι ≫ U.hom) ⟶ U).op s = 0 := by
  exact LinearMap.mem_ker

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a supported section is supported on the same closed subset. -/
theorem sections_restrict (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X))
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    sections Z F U.unop ≤ (sections Z F V.unop).comap (F.val.restrictₛₗ f) := by
  intro s hs
  let WU : U.unop.left.Opens := U.unop.hom ⁻¹ᵁ Z.compl
  let WV : V.unop.left.Opens := V.unop.hom ⁻¹ᵁ Z.compl
  let iU : Scheme.Etale.mk (WU.ι ≫ U.unop.hom) ⟶ U.unop :=
    MorphismProperty.Over.homMk WU.ι
  let iV : Scheme.Etale.mk (WV.ι ≫ V.unop.hom) ⟶ V.unop :=
    MorphismProperty.Over.homMk WV.ι
  have hf : f.unop.left ≫ U.unop.hom = V.unop.hom :=
    MorphismProperty.Over.w (P := (@AlgebraicGeometry.Etale : MorphismProperty Scheme)) f.unop
  have hWV : WV ≤ f.unop.left ⁻¹ᵁ WU := by
    dsimp only [WV, WU]
    rw [← Scheme.Hom.comp_preimage, hf]
  obtain ⟨k, hk⟩ : ∃ k : Scheme.Etale.mk (WV.ι ≫ V.unop.hom) ⟶
      Scheme.Etale.mk (WU.ι ≫ U.unop.hom), k ≫ iU = iV ≫ f.unop := by
    let k : Scheme.Etale.mk (WV.ι ≫ V.unop.hom) ⟶
        Scheme.Etale.mk (WU.ι ≫ U.unop.hom) :=
      MorphismProperty.Over.homMk (f.unop.left.resLE WU WV hWV) (by
        change f.unop.left.resLE WU WV hWV ≫ (WU.ι ≫ U.unop.hom) = WV.ι ≫ V.unop.hom
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hf])
    refine ⟨k, ?_⟩
    apply MorphismProperty.Over.Hom.ext (P := (@AlgebraicGeometry.Etale : MorphismProperty Scheme))
    exact Scheme.Hom.resLE_comp_ι _ hWV
  apply (mem_sections_iff Z F V.unop _).2
  have hcomp := congrArg (fun a => F.val.presheaf.map a) (congrArg Quiver.Hom.op hk)
  have hcomp' := CategoryTheory.congr_fun hcomp s
  simp only [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply] at hcomp'
  change F.val.presheaf.map iV.op (F.val.presheaf.map f s) = 0
  have hs0 : F.val.presheaf.map iU.op s = 0 := (mem_sections_iff Z F U.unop s).1 hs
  exact hcomp'.symm.trans ((congrArg (F.val.presheaf.map k.op) hs0).trans (map_zero _))

/-- The restriction-stable family of section submodules supported on a closed subset. -/
def submodule (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) : F.val.Submodule where
  obj U := sections Z F U.unop
  map f := sections_restrict Z F f

/-- The module presheaf of sections supported on a closed subset of the base scheme. -/
def presheaf (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) :
    _root_.PresheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X).obj :=
  (submodule Z F).toPresheafOfModules

/-- Sections with closed support satisfy étale descent. -/
theorem presheaf_isSheaf (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) :
    Presheaf.IsSheaf X.smallEtaleTopology (presheaf Z F).presheaf := sorry

/-- The ambient module sheaf of sections supported on a closed subset. -/
def sheaf (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) :
    SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X) :=
  ⟨presheaf Z F, presheaf_isSheaf Z F⟩

/-- A module-sheaf morphism sends supported sections to supported sections. -/
theorem map_mem (Z : Closeds X)
    {F G : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)}
    (f : F ⟶ G) (U : X.Etale) (s : F.val.obj (op U)) (hs : s ∈ sections Z F U) :
    f.val.app (op U) s ∈ sections Z G U := by
  let W : U.left.Opens := U.hom ⁻¹ᵁ Z.compl
  let i : Scheme.Etale.mk (W.ι ≫ U.hom) ⟶ U := MorphismProperty.Over.homMk W.ι
  apply (mem_sections_iff Z G U _).2
  calc
    G.val.map i.op (f.val.app (op U) s) =
        f.val.app (op (Scheme.Etale.mk (W.ι ≫ U.hom))) (F.val.map i.op s) :=
      (_root_.PresheafOfModules.naturality_apply f.val i.op s).symm
    _ = f.val.app (op (Scheme.Etale.mk (W.ι ≫ U.hom))) 0 :=
      congrArg (f.val.app (op (Scheme.Etale.mk (W.ι ≫ U.hom))))
        ((mem_sections_iff Z F U s).1 hs)
    _ = 0 := map_zero _

/-- The linear map induced on supported sections by a module-sheaf morphism. -/
def mapApp (Z : Closeds X)
    {F G : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)}
    (f : F ⟶ G) (U : X.Etaleᵒᵖ) : (presheaf Z F).obj U ⟶ (presheaf Z G).obj U :=
  ModuleCat.ofHom ((f.val.app U).hom.restrict (fun s hs ↦ map_mem Z f U.unop s hs))

/-- The maps on supported sections commute with restriction. -/
theorem map_naturality (Z : Closeds X)
    {F G : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)}
    (f : F ⟶ G) {U V : X.Etaleᵒᵖ} (g : U ⟶ V) :
    (presheaf Z F).map g ≫
        (ModuleCat.restrictScalars
          ((AssociatedModule.smallStructureSheaf .etale X).obj.map g).hom).map (mapApp Z f V) =
      mapApp Z f U ≫ (presheaf Z G).map g := by
  ext s
  apply Subtype.ext
  exact _root_.PresheafOfModules.naturality_apply f.val g s.val

/-- The module-sheaf morphism induced on sections with support. -/
def map (Z : Closeds X)
    {F G : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)}
    (f : F ⟶ G) : sheaf Z F ⟶ sheaf Z G where
  val := { app := mapApp Z f, naturality := map_naturality Z f }

/-- The supported-section map preserves identity morphisms. -/
theorem map_id (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) :
    map Z (𝟙 F) = 𝟙 (sheaf Z F) := by
  ext U s
  rfl

/-- The supported-section map preserves composition. -/
theorem map_comp (Z : Closeds X)
    {F G H : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)}
    (f : F ⟶ G) (g : G ⟶ H) : map Z (f ≫ g) = map Z f ≫ map Z g := by
  ext U s
  rfl

/-- The module-valued étale sections-with-support functor. -/
def sectionsFunctor (Z : Closeds X) :
    SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X) ⥤
      SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X) where
  obj := sheaf Z
  map := map Z
  map_id := map_id Z
  map_comp := map_comp Z

/-- Taking sections with support is additive. -/
instance sectionsFunctor_additive (Z : Closeds X) : (sectionsFunctor Z).Additive where
  map_add := by
    intro F G f g
    ext U s
    rfl

variable [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
  [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Module sheaves on the small étale site have injective resolutions. -/
instance hasInjectiveResolutions (X : Scheme.{u})
    [HasSheafify (SmallStandardTopology.etale.topology X) AddCommGrpCat.{u}]
    [(SmallStandardTopology.etale.topology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    HasInjectiveResolutions (SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) := sorry

/-- Global sections with support, evaluated at the identity étale object. -/
abbrev globalSectionsFunctor (Z : Closeds X) :=
  sectionsFunctor Z ⋙ SheafOfModules.evaluation
    (AssociatedModule.smallStructureSheaf .etale X) (op (Scheme.Etale.mk (𝟙 X)))

/-- Global sections with support form an additive functor. -/
instance globalSectionsFunctor_additive (Z : Closeds X) :
    (globalSectionsFunctor Z).Additive :=
  inferInstanceAs (sectionsFunctor Z ⋙
    (SheafOfModules.forget (AssociatedModule.smallStructureSheaf .etale X) ⋙
      _root_.PresheafOfModules.evaluation (AssociatedModule.smallStructureSheaf .etale X).obj
        (op (Scheme.Etale.mk (𝟙 X))))).Additive

/-- The right-derived global sections with support on the small étale site. -/
abbrev cohomology (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) (q : ℕ) :
    ModuleCat Γ(X, ⊤) :=
  ((globalSectionsFunctor Z).rightDerived q).obj F

/-- The ambient étale local-cohomology module sheaf supported on a closed subset. -/
abbrev cohomologySheaf (Z : Closeds X)
    (F : SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X)) (q : ℕ) :
    SheafOfModules.{u} (AssociatedModule.smallStructureSheaf .etale X) :=
  ((sectionsFunctor Z).rightDerived q).obj F

end AlgebraicGeometry.Scheme.Etale.Module.Support
