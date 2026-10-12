/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Module.FunctionField
public import ReasLib.Topology.Presheaf.Localization
public import ReasLib.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Meromorphic sheaves on integral schemes

On an integral scheme, meromorphic functions and meromorphic sections of a quasicoherent module
form constant sheaves with values at the generic point.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped ChangeOfRings nonZeroDivisors

noncomputable section

universe u v

/-- The stalk of the unit from a sheaf to the skyscraper at a specializing point is the
specialization map after the canonical skyscraper-stalk identification. -/
private theorem stalk_unitToSkyscraper_comp_stalkIso
    {Y : TopCat.{u}} {C : Type v} [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    (F : TopCat.Sheaf C Y) (y x : Y) (h : Specializes y x) :
    (TopCat.Presheaf.stalkFunctor C x).map
        ((TopCat.Sheaf.Skyscraper.stalkAdjunction y).unit.app F).hom ≫
        (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y
          (TopCat.Presheaf.stalk F.1 y) h).hom =
      TopCat.Presheaf.stalkSpecializes F.1 h := by
  classical
  apply TopCat.Presheaf.stalk_hom_ext F.1
  intro U hxU
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  simp only [TopCat.Sheaf.Skyscraper.stalkAdjunction,
    stalkSkyscraperSheafAdjunction,
    StalkSkyscraperPresheafAdjunctionAuxs.unit_app,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app]
  erw [dif_pos (h.mem_open U.isOpen hxU)]
  simp only [Functor.id_obj]
  erw [Category.id_comp]
  change (F.presheaf.germ U y _ ≫ eqToHom _) ≫
      (TopCat.Sheaf.Skyscraper.atPoint y
        (F.presheaf.stalk y)).presheaf.germ U x hxU ≫
        (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y
          (F.presheaf.stalk y) h).hom =
    F.presheaf.germ U x hxU ≫ F.presheaf.stalkSpecializes h
  rw [F.presheaf.germ_stalkSpecializes]
  dsimp only [TopCat.Sheaf.Skyscraper.atPoint,
    TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes, skyscraperSheaf,
    TopCat.Sheaf.presheaf]
  simp only [Category.assoc, germ_skyscraperPresheafStalkOfSpecializes_hom]
  erw [eqToHom_trans]
  rw [eqToHom_refl, Category.comp_id]

/-- The stalk of the presheaf-to-skyscraper adjunction unit becomes the specialization map under
the canonical skyscraper-stalk identification. -/
private theorem stalk_presheafUnitToSkyscraper_comp_stalkIso
    {Y : TopCat.{u}} {C : Type v} [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    (P : Y.Presheaf C) (y x : Y) (h : Specializes y x) :
    (TopCat.Presheaf.stalkFunctor C x).map
        ((TopCat.Sheaf.Skyscraper.presheafStalkAdjunction y).unit.app P) ≫
        (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y (P.stalk y) h).hom =
      P.stalkSpecializes h := by
  classical
  apply TopCat.Presheaf.stalk_hom_ext P
  intro U hxU
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  simp only [TopCat.Sheaf.Skyscraper.presheafStalkAdjunction,
    skyscraperSheafForgetAdjunction, skyscraperPresheafStalkAdjunction,
    StalkSkyscraperPresheafAdjunctionAuxs.unit_app,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app]
  erw [dif_pos (h.mem_open U.isOpen hxU)]
  simp only [Functor.id_obj]
  erw [Category.id_comp]
  change (P.germ U y _ ≫ eqToHom _) ≫
      (TopCat.Sheaf.Skyscraper.atPoint y (P.stalk y)).presheaf.germ U x hxU ≫
        (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y (P.stalk y) h).hom =
    P.germ U x hxU ≫ P.stalkSpecializes h
  rw [P.germ_stalkSpecializes]
  dsimp only [TopCat.Sheaf.Skyscraper.atPoint,
    TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes, skyscraperSheaf,
    TopCat.Sheaf.presheaf]
  simp only [Category.assoc, germ_skyscraperPresheafStalkOfSpecializes_hom]
  erw [eqToHom_trans]
  rw [eqToHom_refl, Category.comp_id]

/-- The canonical stalk identification for a skyscraper sheaf is natural in its value. -/
private theorem stalk_skyscraper_map_comp_stalkIso
    {Y : TopCat.{u}} {C : Type v} [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    (y x : Y) (h : Specializes y x) {A B : C} (f : A ⟶ B) :
    (TopCat.Presheaf.stalkFunctor C x).map
        ((TopCat.Sheaf.Skyscraper.functor y).map f).hom ≫
        (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y B h).hom =
      (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y A h).hom ≫ f := by
  classical
  apply TopCat.Presheaf.stalk_hom_ext
    (TopCat.Sheaf.Skyscraper.atPoint y A).presheaf
  intro U hxU
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  dsimp only [TopCat.Sheaf.Skyscraper.functor, skyscraperSheafFunctor,
    skyscraperPresheafFunctor, ObjectProperty.homMk,
    SkyscraperPresheafFunctor.map', SkyscraperPresheafFunctor.map'_app]
  erw [dif_pos (h.mem_open U.isOpen hxU)]
  dsimp only [TopCat.Sheaf.Skyscraper.atPoint,
    TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes, skyscraperSheaf,
    TopCat.Sheaf.presheaf]
  erw [germ_skyscraperPresheafStalkOfSpecializes_hom_assoc,
    germ_skyscraperPresheafStalkOfSpecializes_hom]
  let hy : y ∈ U := h.mem_open U.isOpen hxU
  let hA : (skyscraperPresheaf y A).obj (op U) = A := if_pos hy
  let hB : (skyscraperPresheaf y B).obj (op U) = B := if_pos hy
  change (eqToHom hA ≫ f ≫ eqToHom hB.symm) ≫ eqToHom hB =
    eqToHom hA ≫ f
  simp

/-- The stalk of a constant presheaf is canonically its constant value. -/
private noncomputable def constantPresheafStalkIso
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasColimits C] (A : C) (x : Y) :
    TopCat.Presheaf.stalk ((Functor.const (Opens Y)ᵒᵖ).obj A) x ≅ A := by
  let P : Y.Presheaf C := (Functor.const (Opens Y)ᵒᵖ).obj A
  let c : CategoryTheory.Limits.Cocone
      ((OpenNhds.inclusion x).op ⋙ P) :=
    CategoryTheory.Limits.Cocone.mk A
      { app := fun _ ↦ 𝟙 A
        naturality := fun _ _ _ ↦ by
          change 𝟙 A ≫ 𝟙 A = 𝟙 A ≫ 𝟙 A
          simp }
  let q : P.stalk x ⟶ A := CategoryTheory.Limits.colimit.desc _ c
  refine
    { hom := q
      inv := P.Γgerm x
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply TopCat.Presheaf.stalk_hom_ext P
    intro U hxU
    erw [← Category.assoc]
    dsimp only [q, TopCat.Presheaf.germ]
    erw [CategoryTheory.Limits.colimit.ι_desc]
    dsimp only [c]
    erw [Category.id_comp, Category.comp_id]
    have e :=
      (P.map_germ_eq_Γgerm (i := homOfLE (show U ≤ ⊤ from le_top)) x hxU).symm
    erw [Category.id_comp] at e
    exact eq_of_heq (heq_of_eq e)
  · change P.Γgerm x ≫ q = 𝟙 A
    dsimp only [TopCat.Presheaf.Γgerm, q]
    erw [CategoryTheory.Limits.colimit.ι_desc]

/-- Specialization between stalks of a constant presheaf is the identity after the canonical
identifications with its value. -/
private theorem constantPresheaf_stalkSpecializes_comp_stalkIso
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasColimits C] (A : C) (y x : Y)
    (h : Specializes y x) :
    TopCat.Presheaf.stalkSpecializes
        ((Functor.const (Opens Y)ᵒᵖ).obj A) h ≫
        (constantPresheafStalkIso Y C A y).hom =
      (constantPresheafStalkIso Y C A x).hom := by
  let P : Y.Presheaf C := (Functor.const (Opens Y)ᵒᵖ).obj A
  apply TopCat.Presheaf.stalk_hom_ext P
  intro U hxU
  erw [P.germ_stalkSpecializes_assoc]
  dsimp only [constantPresheafStalkIso]
  erw [CategoryTheory.Limits.colimit.ι_desc,
    CategoryTheory.Limits.colimit.ι_desc]

/-- The constant presheaf maps canonically to the skyscraper at any point with the same value. -/
private noncomputable def constantPresheafToSkyscraper
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    (A : C) (y : Y) :
    (Functor.const (Opens Y)ᵒᵖ).obj A ⟶
      (TopCat.Sheaf.Skyscraper.atPoint y A).presheaf :=
  (TopCat.Sheaf.Skyscraper.presheafStalkAdjunction y).unit.app
      ((Functor.const (Opens Y)ᵒᵖ).obj A) ≫
    ((TopCat.Sheaf.Skyscraper.functor y).map
      (constantPresheafStalkIso Y C A y).hom).hom

/-- On every specialization of the support point, the stalk of the constant-presheaf comparison
is the canonical constant-stalk isomorphism. -/
private theorem stalk_constantPresheafToSkyscraper_comp_stalkIso
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    (A : C) (y x : Y) (h : Specializes y x) :
    (TopCat.Presheaf.stalkFunctor C x).map
        (constantPresheafToSkyscraper Y C A y) ≫
      (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y A h).hom =
      (constantPresheafStalkIso Y C A x).hom := by
  rw [constantPresheafToSkyscraper]
  erw [Functor.map_comp, Category.assoc,
    stalk_skyscraper_map_comp_stalkIso, ← Category.assoc,
    stalk_presheafUnitToSkyscraper_comp_stalkIso,
    constantPresheaf_stalkSpecializes_comp_stalkIso]

/-- The constant sheaf maps canonically to the skyscraper sheaf at any point with the same
value. -/
private noncomputable def constantSheafToSkyscraper
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology Y) C]
    (A : C) (y : Y) :
    (constantSheaf (Opens.grothendieckTopology Y) C).obj A ⟶
      TopCat.Sheaf.Skyscraper.atPoint y A :=
  Sheaf.homEquiv.symm <|
    sheafifyLift (Opens.grothendieckTopology Y)
      (constantPresheafToSkyscraper Y C A y)
      (TopCat.Sheaf.Skyscraper.atPoint y A).property

/-- The constant-sheaf-to-skyscraper comparison extends the canonical presheaf comparison. -/
private theorem constantSheafToSkyscraper_fac
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology Y) C]
    (A : C) (y : Y) :
    toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj A) ≫
        (constantSheafToSkyscraper Y C A y).hom =
      constantPresheafToSkyscraper Y C A y := by
  exact toSheafify_sheafifyLift _ _ _

/-- On every specialization of the support point, the sheafified constant comparison is an
isomorphism on stalks. -/
private theorem stalk_constantSheafToSkyscraper_comp_stalkIso
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology Y) C]
    (A : C) (y x : Y) (h : Specializes y x) :
    (TopCat.Presheaf.stalkFunctor C x).map
        (toSheafify (Opens.grothendieckTopology Y)
          ((Functor.const (Opens Y)ᵒᵖ).obj A)) ≫
      (TopCat.Presheaf.stalkFunctor C x).map
          (constantSheafToSkyscraper Y C A y).hom ≫
        (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y A h).hom =
      (constantPresheafStalkIso Y C A x).hom := by
  erw [← Category.assoc, ← Functor.map_comp,
    constantSheafToSkyscraper_fac,
    stalk_constantPresheafToSkyscraper_comp_stalkIso]

/-- A skyscraper supported at a point specializing to every point is the corresponding constant
sheaf. -/
private theorem skyscraper_isIsomorphic_constantSheaf_of_specializes
    (Y : TopCat.{u}) (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasLimits C]
    [CategoryTheory.Limits.HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology Y) C]
    {FC : C → C → Type u} {CC : C → Type u}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)]
    [ConcreteCategory.{u} C FC]
    [CategoryTheory.Limits.PreservesLimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    [CategoryTheory.Limits.PreservesFilteredColimits
      (forget C)]
    (A : C) (y : Y) (hy : ∀ x : Y, Specializes y x) :
    IsIsomorphic (TopCat.Sheaf.Skyscraper.atPoint y A)
      ((constantSheaf (Opens.grothendieckTopology Y) C).obj A) := by
  let c := constantSheafToSkyscraper Y C A y
  have hc_stalk (x : Y) :
      IsIso ((TopCat.Presheaf.stalkFunctor C x).map c.hom) := by
    let a := (TopCat.Presheaf.stalkFunctor C x).map
      (toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj A))
    let b := (TopCat.Presheaf.stalkFunctor C x).map c.hom
    let s := (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes y A (hy x)).hom
    -- Local instance justification (proof-local temporary data): sheafification preserves the
    -- stalk of the constant presheaf.
    letI : IsIso a := by
      dsimp only [a]
      exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
        x C ((Functor.const (Opens Y)ᵒᵖ).obj A)
    -- Local instance justification (proof-local temporary data): use the canonical skyscraper
    -- stalk isomorphism at a specialization of its support.
    letI : IsIso s := by
      dsimp only [s]
      infer_instance
    -- Local instance justification (proof-local temporary data): use the explicit constant
    -- presheaf stalk isomorphism.
    letI : IsIso (constantPresheafStalkIso Y C A x).hom := by
      infer_instance
    have habs : a ≫ b ≫ s = (constantPresheafStalkIso Y C A x).hom := by
      exact stalk_constantSheafToSkyscraper_comp_stalkIso
        Y C A y x (hy x)
    -- Local instance justification (proof-local temporary data): transport isomorphy across the
    -- proved comparison with the constant-presheaf stalk isomorphism.
    letI : IsIso (a ≫ b ≫ s) := by
      rw [habs]
      infer_instance
    -- Local instance justification (proof-local temporary data): cancel the sheafification
    -- comparison from the left.
    letI : IsIso (b ≫ s) := IsIso.of_isIso_comp_left a (b ≫ s)
    exact IsIso.of_isIso_comp_right b s
  -- Local instance justification (proof-local temporary data): register the proved stalkwise
  -- isomorphisms solely to apply the stalkwise isomorphism criterion.
  letI (x : Y) : IsIso ((TopCat.Presheaf.stalkFunctor C x).map c.hom) :=
    hc_stalk x
  have hc : IsIso c := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso c
  exact ⟨(asIso c).symm⟩

/-- On an integral scheme, each meromorphic-function stalk is the total fraction ring of the
corresponding local ring. -/
private theorem meromorphicFunctionStalk_isLocalization
    (X : Scheme.{u}) [IsIntegral X] (x : X) :
    IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
      (X.meromorphicFunctionSheaf.presheaf.stalk x) := by
  let T := X.presheaf.submonoidPresheafOfStalk fun y ↦
    nonZeroDivisors (X.presheaf.stalk y)
  have hT : TopCat.Presheaf.SectionLocalization.stalkSubmonoid
      (TopCat.Presheaf.SectionLocalization.ofTopCat T) x =
        nonZeroDivisors (X.presheaf.stalk x) := by
    ext z
    constructor
    · rintro ⟨U, hxU, s, rfl⟩
      have hs : s.1 ∈ ⨅ y : U,
          Submonoid.comap (X.presheaf.germ U y.1 y.2).hom
            (nonZeroDivisors (X.presheaf.stalk y.1)) := s.2
      exact Submonoid.mem_iInf.mp hs ⟨x, hxU⟩
    · intro hz
      obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq z
      refine ⟨U, hxU, ⟨s, ?_⟩, rfl⟩
      change s ∈ ⨅ y : U, Submonoid.comap
        (X.presheaf.germ U y.1 y.2).hom
          (nonZeroDivisors (X.presheaf.stalk y.1))
      apply Submonoid.mem_iInf.mpr
      intro y
      change (X.presheaf.germ U y.1 y.2).hom s ∈
        nonZeroDivisors (X.presheaf.stalk y.1)
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hy
      have hs : s = 0 := germ_injective_of_isIntegral X y.1 y.2 (by simpa using hy)
      rw [hs, map_zero] at hz
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hz) rfl
  rw [← hT]
  exact TopCat.Presheaf.SectionLocalization.sheafifiedStalkIsLocalization
    (TopCat.Presheaf.SectionLocalization.ofTopCat T) x

/-- Scalar extension to meromorphic functions commutes with taking the stalk of a module
sheaf. -/
private noncomputable def meromorphicSectionStalkExtensionIso
    (X : Scheme.{u}) (ℱ : X.Modules) (x : X) :
    (ModuleCat.extendScalars
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom).obj
          (RingedSpace.stalkModuleCat ℱ x) ≅
      (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).obj
        (X.meromorphicSectionSheaf ℱ) :=
  (TopCat.Sheaf.ChangeOfRings.Stalk.comparisonIso
      X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom x ℱ) ≪≫
    (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).mapIso
      ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u} (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).symm.app ℱ)

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X]

/-- The meromorphic-function sheaf on an integral scheme is isomorphic to the constant sheaf
with value its function field. -/
theorem meromorphicFunctionSheaf_isIsomorphic_constantFunctionField :
    IsIsomorphic X.meromorphicFunctionSheaf
      ((constantSheaf (Opens.grothendieckTopology X.toTopCat) CommRingCat).obj
        X.functionField) := by
  classical
  let η := genericPoint X
  let F := X.meromorphicFunctionSheaf
  -- Local instance justification (proof-local temporary data): use the proved localization
  -- description at the generic point to form its canonical comparison with the function field.
  letI : IsLocalization (nonZeroDivisors X.functionField) (F.presheaf.stalk η) := by
    exact meromorphicFunctionStalk_isLocalization X η
  let eη : F.presheaf.stalk η ≃ₐ[X.functionField] X.functionField :=
    IsLocalization.algEquiv (nonZeroDivisors X.functionField)
      (F.presheaf.stalk η) X.functionField
  let fη : F.presheaf.stalk η ⟶ X.functionField :=
    CommRingCat.ofHom eη.toRingEquiv.toRingHom
  let φ : F ⟶ TopCat.Sheaf.Skyscraper.atPoint η X.functionField :=
    (TopCat.Sheaf.Skyscraper.stalkAdjunction η).unit.app F ≫
      (TopCat.Sheaf.Skyscraper.functor η).map fη
  have hφ_stalk (x : X) :
      IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map φ.hom) := by
    let h : Specializes η x := (genericPoint_spec X).specializes trivial
    let g : F.presheaf.stalk x ⟶ X.functionField :=
      F.presheaf.stalkSpecializes h ≫ fη
    -- Local instance justification (proof-local temporary data): use the proved localization
    -- description of the meromorphic stalk at `x`.
    letI : IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
        (F.presheaf.stalk x) := meromorphicFunctionStalk_isLocalization X x
    have hg_bijective : Function.Bijective g := by
      apply IsLocalization.bijective (nonZeroDivisors (X.presheaf.stalk x)) g.hom
      ext r
      change eη
          (F.presheaf.stalkSpecializes h
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
              X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom r)) =
        X.presheaf.stalkSpecializes h r
      have hn := TopCat.Presheaf.stalkSpecializes_stalkFunctor_map
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom h
      have hnr := ConcreteCategory.congr_hom hn r
      change
        ((TopCat.Presheaf.stalkFunctor CommRingCat η).map
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom
              (X.presheaf.stalkSpecializes h r) =
          F.presheaf.stalkSpecializes h
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
              X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom r) at hnr
      rw [← hnr]
      exact eη.commutes _
    -- Local instance justification (proof-local temporary data): a bijective morphism in
    -- `CommRingCat` is an isomorphism.
    letI hg : IsIso g := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hg_bijective
    let s :=
      (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes η X.functionField h).hom
    -- Local instance justification (proof-local temporary data): use the canonical skyscraper
    -- stalk isomorphism.
    letI : IsIso s := by
      dsimp only [s]
      infer_instance
    have hcomp :
        (TopCat.Presheaf.stalkFunctor CommRingCat x).map φ.hom ≫ s = g := by
      dsimp only [φ, g]
      erw [Functor.map_comp, Category.assoc,
        stalk_skyscraper_map_comp_stalkIso, ← Category.assoc,
        stalk_unitToSkyscraper_comp_stalkIso]
      rfl
    -- Local instance justification (proof-local temporary data): transport isomorphy across
    -- the computed stalk comparison.
    letI : IsIso
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map φ.hom ≫ s) := by
      rw [hcomp]
      exact hg
    exact IsIso.of_isIso_comp_right _ s
  -- Local instance justification (proof-local temporary data): register the stalkwise
  -- isomorphisms solely for the stalkwise sheaf-isomorphism criterion.
  letI (x : X.toTopCat) : IsIso
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map φ.hom) := hφ_stalk x
  -- Local instance justification (proof-local temporary data): package the stalkwise result as
  -- an isomorphism of sheaves for the ensuing explicit comparison.
  letI hφ : IsIso φ := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso φ
  obtain ⟨e⟩ := skyscraper_isIsomorphic_constantSheaf_of_specializes
    X.toTopCat CommRingCat X.functionField η
      (fun x ↦ (genericPoint_spec X).specializes trivial)
  exact ⟨(@asIso _ _ _ _ φ hφ) ≪≫ e⟩

/-- The meromorphic-function sheaf on an integral scheme is constant. -/
noncomputable instance meromorphicFunctionSheaf_isConstant :
    Sheaf.IsConstant (Opens.grothendieckTopology X.toTopCat)
      X.meromorphicFunctionSheaf := by
  classical
  exact Sheaf.isConstant_of_iso (Opens.grothendieckTopology X.toTopCat)
    (Classical.choice meromorphicFunctionSheaf_isIsomorphic_constantFunctionField)

set_option maxHeartbeats 2000000 in
/-- The stalk map from a module to its meromorphic scalar extension, bundled over the local
ring. -/
private noncomputable def meromorphicSectionStalkUnit (ℱ : X.Modules) (x : X) :
    let r := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom
    let Gx : ModuleCat (X.meromorphicFunctionSheaf.presheaf.stalk x) :=
      (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).obj
        (X.meromorphicSectionSheaf ℱ)
    RingedSpace.stalkModuleCat ℱ x ⟶ (ModuleCat.restrictScalars r).obj Gx :=
  ModuleCat.ExtendRestrictScalarsAdj.Unit.map _ ≫
    (ModuleCat.restrictScalars _).map
      (meromorphicSectionStalkExtensionIso X ℱ x).hom

set_option maxHeartbeats 2000000 in
/-- The bundled localization unit has the underlying canonical map to the meromorphic-section
stalk. -/
private theorem meromorphicSectionStalkUnit_apply (ℱ : X.Modules) (x : X)
    (m : RingedSpace.stalkModuleCat ℱ x) :
    meromorphicSectionStalkUnit ℱ x m =
      X.toLocallyRingedSpace.meromorphicSectionStalkMap ℱ x m := by
  let q := SheafOfModules.RingedSite.ringedSiteStructureMap.{u, u, u}
    X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom
  have hpull :
      (SheafOfModules.PullbackConstruction.adjunction.{u} q).unit.app ℱ ≫
        (SheafOfModules.pushforward.{u} q).map
          ((SheafOfModules.pullbackIso.{u} q).inv.app ℱ) =
        (SheafOfModules.pullbackPushforwardAdjunction.{u} q).unit.app ℱ := by
    exact CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
      (SheafOfModules.PullbackConstruction.adjunction.{u} q)
      (SheafOfModules.pullbackPushforwardAdjunction.{u} q) ℱ
  have hunit :
      (SheafOfModules.ChangeOfRings.extendRestrictAdjunction.{u, u, u, u}
          (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).unit.app ℱ ≫
        (SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).map
            ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
              (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
                X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).inv.app ℱ) =
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (SheafOfModules.RingedSite.ringedSiteStructureMap.{u, u, u}
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).unit.app ℱ := by
    exact SheafOfModules.ChangeOfRings.extendScalarsIso_unit_inv_app
      (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (SheafOfModules.RingedSite.ringedSiteStructureMap.{u, u, u}
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).ofNatIsoRight
          (SheafOfModules.ChangeOfRings.pushforwardIso
            (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
              X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom))) ℱ
  dsimp only [AlgebraicGeometry.LocallyRingedSpace.meromorphicSectionStalkMap]
  rw [hunit]
  let r := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
    X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom
  let M : ModuleCat ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.𝒪.obj) :=
    RingedSpace.stalkModuleCat ℱ x
  -- Local instance justification (defeq pin): expose the bundled source stalk module.
  letI : Module ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.𝒪.obj) M := M.isModule
  have htmul : (ModuleCat.ExtendRestrictScalarsAdj.Unit.map r) m =
      (1 : (TopCat.Presheaf.stalkFunctor CommRingCat x).obj
        X.meromorphicFunctionSheaf.obj) ⊗ₜ[
        (TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.𝒪.obj,
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom] m := rfl
  change ((ModuleCat.restrictScalars r).map
      (meromorphicSectionStalkExtensionIso X ℱ x).hom)
        ((1 : X.meromorphicFunctionSheaf.presheaf.stalk x) ⊗ₜ[
          X.presheaf.stalk x,
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom] m) =
    ((SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).map
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} q).unit.app ℱ)).hom m
  simp [meromorphicSectionStalkExtensionIso,
    TopCat.Sheaf.ChangeOfRings.Stalk.comparisonIso,
    TopCat.Sheaf.ChangeOfRings.Stalk.comparisonApp,
    TopCat.Sheaf.ChangeOfRings.Stalk.constructionToExtension,
    SheafOfModules.ChangeOfRings.pullbackIso,
    TopCat.Sheaf.moduleBaseChangeStalkComparison]
  change (((TopCat.Presheaf.stalkBaseChangeComparison
      X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom ℱ.val x ≫
    TopCat.Sheaf.moduleSheafificationStalkComparison X.meromorphicFunctionSheaf
      ((PresheafOfModules.pullback
        (TopCat.Presheaf.commRingPresheafHomOverId
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom)).obj ℱ.val) x ≫
    (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
      ((SheafOfModules.pullbackIso q).inv.app ℱ) ≫
    (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
      ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
        (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app ℱ) ≫
    (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
      ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
        (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).inv.app ℱ))
      (ModuleCat.ExtendRestrictScalarsAdj.Unit.map r m))) = _
  simp only [CategoryTheory.comp_apply]
  erw [htmul]
  erw [TopCat.Presheaf.stalkBaseChangeComparison_one_tmul]
  have hcancel :
      (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
          ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
            (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
              X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app ℱ) ≫
        (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
          ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
            (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
              X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).inv.app ℱ) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact (SheafOfModules.stalkFunctorOfCommRing
      X.meromorphicFunctionSheaf x).map_id _
  let y := (SheafOfModules.stalkFunctorOfCommRing
    X.meromorphicFunctionSheaf x).map ((SheafOfModules.pullbackIso q).inv.app ℱ)
      (TopCat.Sheaf.moduleSheafificationStalkComparison X.meromorphicFunctionSheaf
        ((PresheafOfModules.pullback
          (TopCat.Presheaf.commRingPresheafHomOverId
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom)).obj ℱ.val) x
        (TopCat.Presheaf.stalkUnderlyingMapToRestricted
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom
          ((PresheafOfModules.pullbackPushforwardAdjunction
            (TopCat.Presheaf.commRingPresheafHomOverId
              X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom)).unit.app ℱ.val) x m))
  have hcancel_apply := ConcreteCategory.congr_hom hcancel y
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hcancel_apply
  change ((SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
      ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
        (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).inv.app ℱ)
    (((SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
      ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
        (SheafOfModules.RingedSite.ringSheafMap.{u, u, u}
          X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app ℱ)) y)) = _
  rw [hcancel_apply]
  have hpullStalk := congrArg
    (fun f ↦ (SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).map f) hpull
  have hpullStalk_apply := ConcreteCategory.congr_hom hpullStalk m
  let z := TopCat.Sheaf.moduleSheafificationStalkComparison X.meromorphicFunctionSheaf
    ((PresheafOfModules.pullback
      (TopCat.Presheaf.commRingPresheafHomOverId
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom)).obj ℱ.val) x
      (TopCat.Presheaf.stalkUnderlyingMapToRestricted
        X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom
        ((PresheafOfModules.pullbackPushforwardAdjunction
          (TopCat.Presheaf.commRingPresheafHomOverId
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom)).unit.app ℱ.val) x m)
  have hy : y = (SheafOfModules.stalkFunctorOfCommRing
      X.meromorphicFunctionSheaf x).map ((SheafOfModules.pullbackIso q).inv.app ℱ) z := rfl
  let P := (PresheafOfModules.pullback q.hom).obj ℱ.val
  let G := (PresheafOfModules.sheafification
    (𝟙 (SheafOfModules.RingedSite.ringSheaf
      (Opens.grothendieckTopology X.toTopCat) X.meromorphicFunctionSheaf).obj)).obj P
  have hconstructionVal :
      ((SheafOfModules.PullbackConstruction.adjunction q).unit.app ℱ).val =
        (PresheafOfModules.pullbackPushforwardAdjunction q.hom).unit.app ℱ.val ≫
          (PresheafOfModules.pushforward q.hom).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (SheafOfModules.RingedSite.ringSheaf
                (Opens.grothendieckTopology X.toTopCat)
                  X.meromorphicFunctionSheaf).obj)).unit.app P) := by
    rfl
  have hconstruction :
      ((SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).map
        ((SheafOfModules.PullbackConstruction.adjunction q).unit.app ℱ)).hom m = z := by
    change PresheafOfModules.stalkMapUnderlying
      ((SheafOfModules.PullbackConstruction.adjunction q).unit.app ℱ).val x m = z
    rw [hconstructionVal]
    change (PresheafOfModules.stalkMapOfCommRing
      ((PresheafOfModules.pullbackPushforwardAdjunction q.hom).unit.app ℱ.val ≫
        (PresheafOfModules.pushforward q.hom).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (SheafOfModules.RingedSite.ringSheaf
              (Opens.grothendieckTopology X.toTopCat)
                X.meromorphicFunctionSheaf).obj)).unit.app P)) x).hom m = z
    rw [PresheafOfModules.stalkMapOfCommRing_comp]
    rfl
  rw [Functor.map_comp] at hpullStalk_apply
  change (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).map
      ((SheafOfModules.pullbackIso q).inv.app ℱ)
        (((SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).map
          ((SheafOfModules.PullbackConstruction.adjunction q).unit.app ℱ)).hom m) = _
    at hpullStalk_apply
  rw [hconstruction] at hpullStalk_apply
  rw [hy]
  exact hpullStalk_apply

set_option maxHeartbeats 2000000 in
/-- The stalk unit for meromorphic scalar extension localizes the original module stalk. -/
private theorem meromorphicSectionStalkUnit_isLocalizedModule
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X) :
    IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x))
      (meromorphicSectionStalkUnit ℱ x).hom := by
  let p := X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom
  let e := meromorphicSectionStalkExtensionIso X ℱ x
  let r := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map p.hom).hom
  let E : ModuleCat (X.meromorphicFunctionSheaf.presheaf.stalk x) :=
    (ModuleCat.extendScalars r).obj (RingedSpace.stalkModuleCat ℱ x)
  let A : ModuleCat (X.presheaf.stalk x) := (ModuleCat.restrictScalars r).obj E
  let G : ModuleCat (X.meromorphicFunctionSheaf.presheaf.stalk x) :=
    (SheafOfModules.stalkFunctorOfCommRing X.meromorphicFunctionSheaf x).obj
      (X.meromorphicSectionSheaf ℱ)
  let B : ModuleCat (X.presheaf.stalk x) := (ModuleCat.restrictScalars r).obj G
  -- Local instance justification (defeq pin): expose the bundled source stalk module.
  letI : Module (X.presheaf.stalk x) A := A.isModule
  -- Local instance justification (defeq pin): expose the bundled target stalk module.
  letI : Module (X.presheaf.stalk x) B := B.isModule
  let a : RingedSpace.stalkModuleCat ℱ x ⟶ A :=
    ModuleCat.ExtendRestrictScalarsAdj.Unit.map r
  let b : A ⟶ B :=
    (ModuleCat.restrictScalars r).map e.hom
  have hunit : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) a.hom := by
    dsimp only [a, r]
    -- Local instance justification (proof-local temporary data): use the meromorphic stalk localization.
    letI : IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
        (X.meromorphicFunctionSheaf.presheaf.stalk x) :=
      meromorphicFunctionStalk_isLocalization X x
    change IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x))
      (TensorProduct.mk (X.presheaf.stalk x)
        (X.meromorphicFunctionSheaf.presheaf.stalk x)
          (RingedSpace.stalkModuleCat ℱ x) 1)
    infer_instance
  have hb : Function.Bijective b.hom := ConcreteCategory.bijective_of_isIso b
  let eb := LinearEquiv.ofBijective b.hom hb
  change IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) (a ≫ b).hom
  exact IsLocalizedModule.of_linearEquiv
    (S := nonZeroDivisors (X.presheaf.stalk x)) a.hom eb

set_option maxHeartbeats 2000000 in
/-- For a quasicoherent module on an integral scheme, the underlying additive sheaf of
meromorphic sections is isomorphic to the constant sheaf with value its generic stalk. -/
theorem meromorphicSectionSheaf_underlying_isIsomorphic_constantGenericStalk
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      ((SheafOfModules.toSheaf
        (SheafOfModules.RingedSite.ringSheaf
          (Opens.grothendieckTopology X.toTopCat) X.meromorphicFunctionSheaf)).obj
            (X.meromorphicSectionSheaf ℱ))
      ((constantSheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
        (AddCommGrpCat.of (RingedSpace.stalkModuleCat ℱ (genericPoint X)))) := by
  classical
  let η := genericPoint X
  let p := X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom
  let G := X.meromorphicSectionSheaf ℱ
  let F : X.toTopCat.Sheaf AddCommGrpCat := (SheafOfModules.toSheaf
    (SheafOfModules.RingedSite.ringSheaf
      (Opens.grothendieckTopology X.toTopCat) X.meromorphicFunctionSheaf)).obj G
  let H : X.Modules :=
    (SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u} p).obj G
  let a : ℱ ⟶ H :=
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction.{u, u, u, u}
      (SheafOfModules.RingedSite.ringSheafMap.{u, u, u} p)).unit.app ℱ ≫
      (SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u} p).map
        ((SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
          (SheafOfModules.RingedSite.ringSheafMap.{u, u, u} p)).inv.app ℱ)
  let d (x : X) := TopCat.Presheaf.stalkModuleMapToRestrict p.hom
    (𝟙 H.val) x
  let uη := meromorphicSectionStalkUnit ℱ η
  let tη := Scheme.Modules.stalkToFunctionField ℱ η
  -- Local instance justification (proof-local temporary data): localize the generic-stalk unit.
  letI huη : IsLocalizedModule (nonZeroDivisors X.functionField) uη.hom :=
    meromorphicSectionStalkUnit_isLocalizedModule ℱ η
  -- Local instance justification (proof-local temporary data): localize the generic-stalk target map.
  letI htη : IsLocalizedModule (nonZeroDivisors X.functionField) tη.hom :=
    Scheme.Modules.isLocalizedModule_stalkToFunctionField ℱ η
  let eη := IsLocalizedModule.linearEquiv
    (nonZeroDivisors X.functionField) uη.hom tη.hom
  let fη : F.presheaf.stalk η ⟶
      AddCommGrpCat.of (RingedSpace.stalkModuleCat ℱ η) :=
    AddCommGrpCat.ofHom eη.toLinearMap.toAddMonoidHom
  let φ : F ⟶ TopCat.Sheaf.Skyscraper.atPoint η
      (AddCommGrpCat.of (RingedSpace.stalkModuleCat ℱ η)) :=
    (TopCat.Sheaf.Skyscraper.stalkAdjunction η).unit.app F ≫
      (TopCat.Sheaf.Skyscraper.functor η).map fη
  have hφ_stalk (x : X) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom) := by
    let h : Specializes η x := (genericPoint_spec X).specializes trivial
    let ux := meromorphicSectionStalkUnit ℱ x
    let tx := Scheme.Modules.stalkToFunctionField ℱ x
    have hd_apply (y : X) (m : RingedSpace.stalkModuleCat H y) :
        d y m = m := by
      dsimp only [d, TopCat.Presheaf.stalkModuleMapToRestrict,
        TopCat.Presheaf.stalkUnderlyingMapToRestricted]
      change (PresheafOfModules.stalkMapOfCommRing (𝟙 H.val) y).hom m = m
      have hm := ConcreteCategory.congr_hom
        (PresheafOfModules.stalkMapOfCommRing_id H.val y) m
      exact hm
    have hd_bijective (y : X) : Function.Bijective (d y).hom := by
      refine Function.bijective_iff_has_inverse.mpr ⟨fun m ↦ m, ?_, ?_⟩
      · intro m
        exact hd_apply y m
      · intro m
        exact hd_apply y m
    -- Local instance justification (proof-local temporary data): use the explicit stalk inverse.
    letI hd_isIso (y : X) : IsIso (d y) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hd_bijective y
    have hd_inv_apply (y : X)
        (m : (ModuleCat.restrictScalars
          ((TopCat.Presheaf.stalkFunctor CommRingCat y).map p.hom).hom).obj
            ((SheafOfModules.stalkFunctorOfCommRing
              X.meromorphicFunctionSheaf y).obj G)) :
        inv (d y) m = m := by
      apply (hd_bijective y).1
      have hm := ConcreteCategory.congr_hom
        (IsIso.inv_hom_id_assoc (d y) (𝟙 _)) m
      exact hm.trans (hd_apply y m).symm
    let g :=
      inv (d x) ≫ Scheme.Modules.stalkToFunctionField H x ≫
        (ModuleCat.restrictScalars
          (algebraMap (X.presheaf.stalk x) X.functionField)).map (d η) ≫
        (ModuleCat.restrictScalars
          (algebraMap (X.presheaf.stalk x) X.functionField)).map eη.toModuleIso.hom
    have hux : RingedSpace.moduleStalkHom x a ≫ d x = ux := by
      ext m
      change d x (RingedSpace.moduleStalkHom x a m) = ux m
      rw [hd_apply, meromorphicSectionStalkUnit_apply]
      rfl
    have huη' : RingedSpace.moduleStalkHom η a ≫ d η = uη := by
      ext m
      change d η (RingedSpace.moduleStalkHom η a m) = uη m
      rw [hd_apply, meromorphicSectionStalkUnit_apply]
      rfl
    have hnat := Scheme.Modules.stalkToFunctionField_naturality a x
    have hug : ux ≫ g = tx ≫
        (ModuleCat.restrictScalars
          (algebraMap (X.presheaf.stalk x) X.functionField)).map tη := by
      dsimp only [g]
      ext m
      change eη (d η (Scheme.Modules.stalkToFunctionField H x
        (inv (d x) (ux m)))) = tη (tx m)
      have hinv : inv (d x) (ux m) = RingedSpace.moduleStalkHom x a m := by
        calc
          inv (d x) (ux m) =
              inv (d x) (d x (RingedSpace.moduleStalkHom x a m)) :=
            congrArg (fun z ↦ inv (d x) z)
              (ConcreteCategory.congr_hom hux m).symm
          _ = RingedSpace.moduleStalkHom x a m :=
            ConcreteCategory.congr_hom (IsIso.hom_inv_id (d x)) _
      calc
        eη (d η (Scheme.Modules.stalkToFunctionField H x
            (inv (d x) (ux m)))) =
            eη (d η (Scheme.Modules.stalkToFunctionField H x
              (RingedSpace.moduleStalkHom x a m))) :=
          congrArg (fun z ↦ eη (d η (Scheme.Modules.stalkToFunctionField H x z))) hinv
        _ = eη (d η (RingedSpace.moduleStalkHom η a (tx m))) :=
          congrArg (fun z ↦ eη (d η z))
            (ConcreteCategory.congr_hom hnat m).symm
        _ = eη (uη (tx m)) :=
          congrArg eη (ConcreteCategory.congr_hom huη' (tx m))
        _ = tη (tx m) := IsLocalizedModule.linearEquiv_apply
          (nonZeroDivisors X.functionField) uη.hom tη.hom (tx m)
    have htη_bijective : Function.Bijective tη.hom := by
      constructor
      · intro m n hmn
        change TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
          ((genericPoint_spec X).specializes trivial) m =
            TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
              ((genericPoint_spec X).specializes trivial) n at hmn
        rw [show ((genericPoint_spec X).specializes trivial) =
          specializes_refl η from Subsingleton.elim _ _,
          TopCat.Presheaf.stalkSpecializes_refl] at hmn
        exact hmn
      · intro m
        refine ⟨m, ?_⟩
        change TopCat.Presheaf.stalkSpecializes ℱ.val.presheaf
          ((genericPoint_spec X).specializes trivial) m = m
        simpa using ConcreteCategory.congr_hom
          (TopCat.Presheaf.stalkSpecializes_refl ℱ.val.presheaf η) m
    have hrtη_bijective : Function.Bijective
        ((ModuleCat.restrictScalars
          (algebraMap (X.presheaf.stalk x) X.functionField)).map tη).hom :=
      htη_bijective
    let etη := LinearEquiv.ofBijective
      ((ModuleCat.restrictScalars
        (algebraMap (X.presheaf.stalk x) X.functionField)).map tη).hom
        hrtη_bijective
    -- Local instance justification (proof-local temporary data): localize the stalk-to-field map.
    letI htx : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) tx.hom :=
      Scheme.Modules.isLocalizedModule_stalkToFunctionField ℱ x
    -- Local instance justification (proof-local temporary data): transport localization across etη.
    letI htxη : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x))
        (tx ≫ (ModuleCat.restrictScalars
          (algebraMap (X.presheaf.stalk x) X.functionField)).map tη).hom := by
      change IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x))
        (etη.toLinearMap.comp tx.hom)
      infer_instance
    -- Local instance justification (proof-local temporary data): transfer localization along hug.
    letI hugLoc : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x))
        (ux ≫ g).hom := by
      rw [hug]
      infer_instance
    -- Local instance justification (proof-local temporary data): localize the meromorphic-section unit.
    letI huxLoc : IsLocalizedModule (nonZeroDivisors (X.presheaf.stalk x)) ux.hom :=
      meromorphicSectionStalkUnit_isLocalizedModule ℱ x
    let ex := IsLocalizedModule.linearEquiv
      (nonZeroDivisors (X.presheaf.stalk x)) ux.hom (ux ≫ g).hom
    have hex : ex.toLinearMap = g.hom := by
      exact IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp
        (nonZeroDivisors (X.presheaf.stalk x)) ux.hom g.hom
    have hg_bijective : Function.Bijective g.hom := by
      rw [← hex]
      exact ex.bijective
    let g' : F.presheaf.stalk x ⟶
        AddCommGrpCat.of (RingedSpace.stalkModuleCat ℱ η) :=
      AddCommGrpCat.ofHom g.hom.toAddMonoidHom
    let s := (TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes η
      (AddCommGrpCat.of (RingedSpace.stalkModuleCat ℱ η)) h).hom
    -- Local instance justification (proof-local temporary data): package the bijectivity of g.
    letI hg' : IsIso g' := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact hg_bijective
    -- Local instance justification (proof-local temporary data): use the skyscraper stalk isomorphism.
    letI hs : IsIso s := by
      dsimp only [s]
      infer_instance
    have hg_apply (m : F.presheaf.stalk x) :
        g m = eη (F.presheaf.stalkSpecializes h m) := by
      change eη (d η (Scheme.Modules.stalkToFunctionField H x (inv (d x) m))) =
        eη (F.presheaf.stalkSpecializes h m)
      rw [hd_apply, Scheme.Modules.stalkToFunctionField_apply, hd_inv_apply]
      rfl
    have hcomp :
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom ≫ s = g' := by
      dsimp only [φ, g']
      erw [Functor.map_comp, Category.assoc,
        stalk_skyscraper_map_comp_stalkIso, ← Category.assoc,
        stalk_unitToSkyscraper_comp_stalkIso]
      ext m
      exact (hg_apply m).symm
    -- Local instance justification (proof-local temporary data): transport isomorphy along hcomp.
    letI : IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom ≫ s) := by
      rw [hcomp]
      exact hg'
    exact IsIso.of_isIso_comp_right _ s
  -- Local instance justification (proof-local temporary data): apply the stalkwise isomorphism criterion.
  letI (x : X.toTopCat) : IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ.hom) := hφ_stalk x
  -- Local instance justification (proof-local temporary data): package the stalkwise result.
  letI hφ : IsIso φ := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso φ
  obtain ⟨e⟩ := skyscraper_isIsomorphic_constantSheaf_of_specializes
    X.toTopCat AddCommGrpCat
      (AddCommGrpCat.of (RingedSpace.stalkModuleCat ℱ η)) η
        (fun x ↦ (genericPoint_spec X).specializes trivial)
  exact ⟨(@asIso _ _ _ _ φ hφ) ≪≫ e⟩

end AlgebraicGeometry.Scheme
