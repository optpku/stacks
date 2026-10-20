/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Meromorphic
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Stalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Tactic.CrossRefAttribute
import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.NoEmbeddedPoints
import ReasLib.AlgebraicGeometry.Scheme.Module.MeromorphicSection.Reduced

/-!
# Regular meromorphic sections of invertible modules

An invertible module admits a regular meromorphic section when the scheme is integral, when it is
reduced with finitely many irreducible components on quasi-compact opens, or when it is locally
Noetherian without embedded points.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The stalk of a constant presheaf is canonically its constant value. -/
private noncomputable def constantPresheafStalkIsoForMeromorphicSections
    {Y : TopCat.{u}} (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasColimits C] (A : C) (x : Y) :
    TopCat.Presheaf.stalk ((Functor.const (Opens Y)ᵒᵖ).obj A) x ≅ A := by
  let P : Y.Presheaf C := (Functor.const (Opens Y)ᵒᵖ).obj A
  let c : CategoryTheory.Limits.Cocone ((OpenNhds.inclusion x).op ⋙ P) :=
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

/-- The stalk of a constant sheaf is canonically isomorphic to its constant value. -/
private noncomputable def constantSheafStalkIsoForMeromorphicSections
    {Y : TopCat.{u}} (C : Type v) [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology Y) C]
    (A : C) (x : Y) :
    TopCat.Presheaf.stalk
        ((constantSheaf (Opens.grothendieckTopology Y) C).obj A).1 x ≅ A := by
  let P : Y.Presheaf C := (Functor.const (Opens Y)ᵒᵖ).obj A
  let a := (TopCat.Presheaf.stalkFunctor C x).map
    (toSheafify (Opens.grothendieckTopology Y) P)
  have ha : IsIso a := by
    dsimp only [a, P]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x C _
  exact (@asIso _ _ _ _ a ha).symm ≪≫
    constantPresheafStalkIsoForMeromorphicSections C A x

/-- Specialization maps of a sheaf isomorphic to a constant sheaf are isomorphisms. -/
private theorem stalkSpecializesIsIsoOfIsomorphicConstant
    {Y : TopCat.{u}} {C : Type v} [Category.{u} C]
    [CategoryTheory.Limits.HasTerminal C] [CategoryTheory.Limits.HasColimits C]
    [HasWeakSheafify (Opens.grothendieckTopology Y) C]
    (F : Y.Sheaf C) (A : C)
    (hF : IsIsomorphic F
      ((constantSheaf (Opens.grothendieckTopology Y) C).obj A))
    {x y : Y} (h : x ⤳ y) : IsIso (F.presheaf.stalkSpecializes h) := by
  classical
  let P : Y.Presheaf C := (Functor.const (Opens Y)ᵒᵖ).obj A
  let qx := constantPresheafStalkIsoForMeromorphicSections C A x
  let qy := constantPresheafStalkIsoForMeromorphicSections C A y
  have hP : P.stalkSpecializes h ≫ qx.hom = qy.hom := by
    apply TopCat.Presheaf.stalk_hom_ext P
    intro U hyU
    erw [P.germ_stalkSpecializes_assoc]
    dsimp only [qx, qy, constantPresheafStalkIsoForMeromorphicSections]
    erw [CategoryTheory.Limits.colimit.ι_desc,
      CategoryTheory.Limits.colimit.ι_desc]
  -- Local instance justification (proof-local temporary data): identify constant-presheaf stalks.
  letI hPsp : IsIso (P.stalkSpecializes h) := by
    -- Local instance justification (proof-local temporary data): use the constant-stalk comparison.
    haveI : IsIso (P.stalkSpecializes h ≫ qx.hom) := by
      rw [hP]
      infer_instance
    exact IsIso.of_isIso_comp_right _ qx.hom
  let Q := (constantSheaf (Opens.grothendieckTopology Y) C).obj A
  let a (z : Y) := (TopCat.Presheaf.stalkFunctor C z).map
    (toSheafify (Opens.grothendieckTopology Y) P)
  -- Local instance justification (proof-local temporary data): sheafification preserves the x-stalk.
  letI hax : IsIso (a x) := by
    dsimp only [a, P]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x C _
  -- Local instance justification (proof-local temporary data): sheafification preserves the y-stalk.
  letI hay : IsIso (a y) := by
    dsimp only [a, P]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y C _
  have hQ : P.stalkSpecializes h ≫ a x = a y ≫
      TopCat.Presheaf.stalkSpecializes Q.1 h :=
    TopCat.Presheaf.stalkSpecializes_stalkFunctor_map
      (toSheafify (Opens.grothendieckTopology Y) P) h
  -- Local instance justification (proof-local temporary data): cancel the sheafification comparisons.
  letI hQsp : IsIso (TopCat.Presheaf.stalkSpecializes Q.1 h) := by
    -- Local instance justification (proof-local temporary data): use the specialization square.
    haveI : IsIso (a y ≫ TopCat.Presheaf.stalkSpecializes Q.1 h) := by
      rw [← hQ]
      exact IsIso.comp_isIso' hPsp hax
    exact IsIso.of_isIso_comp_left (a y) _
  let e := Classical.choice hF
  -- Local instance justification (proof-local temporary data): apply the chosen isomorphism at x.
  letI hex : IsIso ((TopCat.Presheaf.stalkFunctor C x).map e.hom.hom) := by
    infer_instance
  -- Local instance justification (proof-local temporary data): apply the chosen isomorphism at y.
  letI hey : IsIso ((TopCat.Presheaf.stalkFunctor C y).map e.hom.hom) := by
    infer_instance
  have he : F.presheaf.stalkSpecializes h ≫
      (TopCat.Presheaf.stalkFunctor C x).map e.hom.hom =
        (TopCat.Presheaf.stalkFunctor C y).map e.hom.hom ≫
          TopCat.Presheaf.stalkSpecializes Q.1 h :=
    TopCat.Presheaf.stalkSpecializes_stalkFunctor_map e.hom.hom h
  -- Local instance justification (proof-local temporary data): use the naturality square.
  haveI : IsIso (F.presheaf.stalkSpecializes h ≫
      (TopCat.Presheaf.stalkFunctor C x).map e.hom.hom) := by
    rw [he]
    exact IsIso.comp_isIso' hey hQsp
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (F.presheaf.stalkSpecializes h)
    ((TopCat.Presheaf.stalkFunctor C x).map e.hom.hom) hex inferInstance

/-- On a space with a generic point, the generic germ is injective for a sheaf isomorphic to a
constant sheaf. -/
private theorem genericGermInjectiveOfIsomorphicConstant
    (X : Scheme.{u}) [IsIntegral X] (F : X.toTopCat.Sheaf AddCommGrpCat.{u})
    (A : AddCommGrpCat.{u})
    (hF : IsIsomorphic F
      ((constantSheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj A)) :
    Function.Injective (F.presheaf.Γgerm (genericPoint X)).hom := by
  intro s t hst
  apply TopCat.Presheaf.section_ext F ⊤ s t
  intro x hx
  let h : Specializes (genericPoint X) x := (genericPoint_spec X).specializes trivial
  -- Local instance justification (proof-local temporary data): compare with constant-sheaf specialization.
  letI : IsIso (F.presheaf.stalkSpecializes h) :=
    stalkSpecializesIsIsoOfIsomorphicConstant F A hF h
  apply (ConcreteCategory.bijective_of_isIso (F.presheaf.stalkSpecializes h)).1
  simpa only [TopCat.Presheaf.Γgerm,
    TopCat.Presheaf.germ_stalkSpecializes_apply] using hst

/-- The stalk map classified by a global section sends the scalar `1` to the section germ. -/
private theorem stalkMapUnitSection_apply_one
    {Y : TopCat.{u}} (𝒪 : Y.Sheaf CommRingCat.{u})
    (M : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪))
    (s : M.sections) (x : Y) :
    (((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).map
      (M.unitHomEquiv.symm s)).hom
        ((SheafOfModules.unitStalkLinearEquiv 𝒪 x).symm 1)) =
      SheafOfModules.sectionGermOfCommRing s x := by
  have hsource :
      (SheafOfModules.unitStalkLinearEquiv 𝒪 x).symm 1 =
        TopCat.Presheaf.Γgerm
          (SheafOfModules.unit
            (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.presheaf x
              (1 : 𝒪.presheaf.obj (Opposite.op (⊤ : Opens Y))) := by
    apply (SheafOfModules.unitStalkLinearEquiv 𝒪 x).injective
    rw [LinearEquiv.apply_symm_apply]
    simp only [TopCat.Presheaf.Γgerm]
    change 1 = SheafOfModules.unitStalkToRingStalk 𝒪 x
      (TopCat.Presheaf.germ
        (SheafOfModules.unit (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.presheaf
          ⊤ x (Set.mem_univ x)
            (1 : 𝒪.presheaf.obj (Opposite.op (⊤ : Opens Y))))
    rw [SheafOfModules.unitStalkToRingStalk_germ]
    exact (𝒪.presheaf.germ ⊤ x (Set.mem_univ x)).hom.map_one.symm
  rw [hsource]
  simp only [TopCat.Presheaf.Γgerm]
  erw [SheafOfModules.stalkFunctorOfCommRing_map_germ]
  apply congrArg (fun m ↦
    TopCat.Presheaf.germ M.val.presheaf ⊤ x (Set.mem_univ x) m)
  have hs := congrArg
    (fun t : M.sections ↦ t.1 (Opposite.op (⊤ : Opens Y)))
    (M.unitHomEquiv.apply_symm_apply s)
  exact hs

/-- Specialization of unit-module stalks agrees with specialization of the underlying ring
stalks under the canonical linear equivalences. -/
private theorem unitStalkLinearEquiv_stalkSpecializes
    {Y : TopCat.{u}} (𝒪 : Y.Sheaf CommRingCat.{u})
    {x y : Y} (h : x ⤳ y)
    (m : (SheafOfModules.stalkFunctorOfCommRing 𝒪 y).obj
      (SheafOfModules.unit (TopCat.Sheaf.ringSheafOfComm 𝒪))) :
    SheafOfModules.unitStalkLinearEquiv 𝒪 x
        (TopCat.Presheaf.stalkSpecializes
          (SheafOfModules.unit
            (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.presheaf h m) =
      TopCat.Presheaf.stalkSpecializes 𝒪.1 h
        (SheafOfModules.unitStalkLinearEquiv 𝒪 y m) := by
  obtain ⟨U, hyU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (SheafOfModules.unit
      (TopCat.Sheaf.ringSheafOfComm 𝒪)).val.presheaf m
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply,
    SheafOfModules.unitStalkLinearEquiv_apply,
    SheafOfModules.unitStalkToRingStalk_germ,
    SheafOfModules.unitStalkLinearEquiv_apply,
    SheafOfModules.unitStalkToRingStalk_germ,
    TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- On an integral scheme, regularity of a meromorphic section of an invertible module is
equivalent to nonvanishing. -/
private theorem isRegularMeromorphicSection_iff_ne_zero_of_isIntegral
    (X : Scheme.{u}) [IsIntegral X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) :
    X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s ↔ s ≠ 0 := by
  classical
  let η := genericPoint X
  let K := X.toLocallyRingedSpace.meromorphicFunctionSheaf
  let G := X.toLocallyRingedSpace.meromorphicSectionSheaf ℒ
  let eK := Classical.choice
    (Scheme.meromorphicFunctionSheaf_isIsomorphic_constantFunctionField (X := X))
  let eKη : K.presheaf.stalk η ≅ X.functionField :=
    (TopCat.Presheaf.stalkFunctor CommRingCat η).mapIso
        ((sheafToPresheaf (Opens.grothendieckTopology X.toTopCat)
          CommRingCat).mapIso eK) ≪≫
      constantSheafStalkIsoForMeromorphicSections
        CommRingCat X.functionField η
  let hKField : IsField (K.presheaf.stalk η) :=
    eKη.commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField X.functionField)
  -- Local instance justification (proof-local temporary data): transport the function-field structure.
  letI : Field (K.presheaf.stalk η) := hKField.toField
  let f := X.toLocallyRingedSpace.meromorphicSectionMap ℒ s
  let fη := (SheafOfModules.stalkFunctorOfCommRing K η).map f
  constructor
  · intro hs
    intro hzero
    have hfη : Function.Injective fη.hom :=
      (SheafOfModules.mono_iff_stalkFunctorOfCommRing_map_injective K f).1 hs η
    have hkey :
        fη.hom ((SheafOfModules.unitStalkLinearEquiv K η).symm 1) =
          SheafOfModules.sectionGermOfCommRing s η := by
      exact stalkMapUnitSection_apply_one K G s η
    have hzeroGerm : SheafOfModules.sectionGermOfCommRing s η = 0 := by
      rw [hzero]
      change (TopCat.Presheaf.Γgerm G.val.presheaf η)
        (0 : G.val.obj (Opposite.op (⊤ : Opens X.toTopCat))) = 0
      exact map_zero _
    have hu : (SheafOfModules.unitStalkLinearEquiv K η).symm 1 = 0 := by
      apply hfη
      rw [map_zero, hkey, hzeroGerm]
    have hu' : (1 : K.presheaf.stalk η) = 0 := by
      calc
        1 = SheafOfModules.unitStalkLinearEquiv K η
            ((SheafOfModules.unitStalkLinearEquiv K η).symm 1) :=
          ((SheafOfModules.unitStalkLinearEquiv K η).apply_symm_apply 1).symm
        _ = SheafOfModules.unitStalkLinearEquiv K η 0 := congrArg _ hu
        _ = 0 := map_zero _
    exact one_ne_zero hu'
  · intro hs
    let F : X.toTopCat.Sheaf AddCommGrpCat :=
      (SheafOfModules.toSheaf
        (SheafOfModules.RingedSite.ringSheaf
          (Opens.grothendieckTopology X.toTopCat) K)).obj G
    have hF : IsIsomorphic F
        ((constantSheaf (Opens.grothendieckTopology X.toTopCat)
          AddCommGrpCat).obj
            (AddCommGrpCat.of
              (RingedSpace.stalkModuleCat ℒ (genericPoint X)))) := by
      exact Scheme.meromorphicSectionSheaf_underlying_isIsomorphic_constantGenericStalk ℒ
    have hsTop : s.1 (Opposite.op (⊤ : Opens X.toTopCat)) ≠ 0 := by
      intro hsTopZero
      apply hs
      apply PresheafOfModules.sections_ext
      intro U
      calc
        s.1 U = G.val.map (homOfLE le_top).op
            (s.1 (Opposite.op (⊤ : Opens X.toTopCat))) :=
          (s.2 (homOfLE le_top).op).symm
        _ = G.val.map (homOfLE le_top).op 0 := congrArg _ hsTopZero
        _ = 0 := (G.val.map (homOfLE le_top).op).hom.map_zero
    have hΓ : Function.Injective
        (F.presheaf.Γgerm (genericPoint X)).hom :=
      genericGermInjectiveOfIsomorphicConstant X F
        (AddCommGrpCat.of
          (RingedSpace.stalkModuleCat ℒ (genericPoint X))) hF
    have hgerm : SheafOfModules.sectionGermOfCommRing s η ≠ 0 := by
      intro hgermZero
      apply hsTop
      apply hΓ
      change (F.presheaf.Γgerm η).hom
        (s.1 (Opposite.op (⊤ : Opens X.toTopCat))) = 0 at hgermZero
      exact hgermZero.trans
        ((F.presheaf.Γgerm (genericPoint X)).hom.map_zero).symm
    have hkey :
        fη.hom ((SheafOfModules.unitStalkLinearEquiv K η).symm 1) =
          SheafOfModules.sectionGermOfCommRing s η := by
      exact stalkMapUnitSection_apply_one K G s η
    let g := fη.hom.comp
      (SheafOfModules.unitStalkLinearEquiv K η).symm.toLinearMap
    have hg : g ≠ 0 := by
      intro hzero
      apply hgerm
      rw [← hkey]
      have hzeroOne := LinearMap.congr_fun hzero 1
      change fη.hom ((SheafOfModules.unitStalkLinearEquiv K η).symm 1) = 0
        at hzeroOne
      exact hzeroOne
    have hgInjective : Function.Injective g := LinearMap.injective_of_ne_zero hg
    have hfη : Function.Injective fη.hom := by
      intro a b hab
      apply (SheafOfModules.unitStalkLinearEquiv K η).injective
      apply hgInjective
      change fη.hom ((SheafOfModules.unitStalkLinearEquiv K η).symm
          (SheafOfModules.unitStalkLinearEquiv K η a)) =
        fη.hom ((SheafOfModules.unitStalkLinearEquiv K η).symm
          (SheafOfModules.unitStalkLinearEquiv K η b))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact hab
    apply (SheafOfModules.mono_iff_stalkFunctorOfCommRing_map_injective K f).2
    intro x
    let h : Specializes (genericPoint X) x :=
      (genericPoint_spec X).specializes trivial
    let ksp := TopCat.Presheaf.stalkSpecializes K.1 h
    let usp := TopCat.Presheaf.stalkSpecializes
      (SheafOfModules.unit
        (TopCat.Sheaf.ringSheafOfComm K)).val.presheaf h
    -- Local instance justification (proof-local temporary data): use the constant-sheaf comparison.
    letI hksp : IsIso ksp := by
      exact stalkSpecializesIsIsoOfIsomorphicConstant K X.functionField
        ⟨eK⟩ h
    have huspBijective : Function.Bijective usp := by
      constructor
      · intro a b hab
        apply (SheafOfModules.unitStalkLinearEquiv K x).injective
        apply (ConcreteCategory.bijective_of_isIso ksp).1
        rw [← unitStalkLinearEquiv_stalkSpecializes K h a,
          ← unitStalkLinearEquiv_stalkSpecializes K h b, hab]
      · intro b
        obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso ksp).2
          (SheafOfModules.unitStalkLinearEquiv K (genericPoint X) b)
        refine ⟨(SheafOfModules.unitStalkLinearEquiv K x).symm r, ?_⟩
        apply (SheafOfModules.unitStalkLinearEquiv K (genericPoint X)).injective
        rw [unitStalkLinearEquiv_stalkSpecializes K h,
          LinearEquiv.apply_symm_apply, hr]
    -- Local instance justification (proof-local temporary data): package the unit specialization.
    letI husp : IsIso usp := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact huspBijective
    let fx := (SheafOfModules.stalkFunctorOfCommRing K x).map f
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso usp).1
    apply hfη
    let gsp := TopCat.Presheaf.stalkSpecializes G.val.presheaf h
    have hnat := TopCat.Presheaf.stalkSpecializes_stalkFunctor_map
      ((PresheafOfModules.toPresheaf _).map f.val) h
    have hnata := ConcreteCategory.congr_hom hnat a
    have hnatb := ConcreteCategory.congr_hom hnat b
    change fη.hom (usp a) = gsp (fx.hom a) at hnata
    change fη.hom (usp b) = gsp (fx.hom b) at hnatb
    exact hnata.trans ((congrArg gsp hab).trans hnatb.symm)

/-- An invertible module on an integral scheme has a regular meromorphic section. -/
@[stacks 02OZ "integral case"]
theorem exists_regularMeromorphicSection_of_isIntegral
    [IsIntegral X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s := by
  classical
  let η := genericPoint X
  let K := X.toLocallyRingedSpace.meromorphicFunctionSheaf
  let G := X.toLocallyRingedSpace.meromorphicSectionSheaf ℒ
  let F : X.toTopCat.Sheaf AddCommGrpCat :=
    (SheafOfModules.toSheaf
      (SheafOfModules.RingedSite.ringSheaf
        (Opens.grothendieckTopology X.toTopCat) K)).obj G
  let A : AddCommGrpCat := AddCommGrpCat.of
    (RingedSpace.stalkModuleCat ℒ η)
  let P : X.toTopCat.Presheaf AddCommGrpCat :=
    (Functor.const (Opens X.toTopCat)ᵒᵖ).obj A
  let Q : X.toTopCat.Sheaf AddCommGrpCat :=
    (constantSheaf (Opens.grothendieckTopology X.toTopCat)
      AddCommGrpCat).obj A
  let e := Classical.choice
    (Scheme.meromorphicSectionSheaf_underlying_isIsomorphic_constantGenericStalk ℒ)
  let a := toSheafify (Opens.grothendieckTopology X.toTopCat) P
  let c : Q.presheaf.obj (Opposite.op (⊤ : Opens X.toTopCat)) :=
    a.app (Opposite.op (⊤ : Opens X.toTopCat))
      (Scheme.Modules.Invertible.stalkGenerator ℒ)
  let m : G.val.presheaf.obj (Opposite.op (⊤ : Opens X.toTopCat)) :=
    e.inv.hom.app (Opposite.op (⊤ : Opens X.toTopCat)) c
  let Y : RingedSpace.{u} :=
    { carrier := X.toTopCat
      presheaf := K.1
      IsSheaf := K.2 }
  let t : G.sections := RingedSpace.sectionFromTop (X := Y) G m
  let q := constantPresheafStalkIsoForMeromorphicSections
    AddCommGrpCat A η
  have hGenerator : Scheme.Modules.Invertible.stalkGenerator ℒ ≠ 0 :=
    Scheme.Modules.Invertible.stalkGenerator_ne_zero ℒ
  have hPGenerator : P.Γgerm η
      (Scheme.Modules.Invertible.stalkGenerator ℒ) ≠ 0 := by
    intro hzero
    apply hGenerator
    apply (ConcreteCategory.bijective_of_isIso q.inv).1
    change P.Γgerm η (Scheme.Modules.Invertible.stalkGenerator ℒ) = q.inv 0
    rw [hzero, map_zero]
    rfl
  -- Local instance justification (proof-local temporary data): sheafification preserves the generic stalk.
  letI haη : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat η).map a) := by
    dsimp only [a, P]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso η AddCommGrpCat _
  have hc : c ≠ 0 := by
    intro hzero
    apply hPGenerator
    apply (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat η).map a)).1
    have hnat := TopCat.Presheaf.stalkFunctor_map_germ_apply
      (F := P) (G := Q.1) ⊤ η (Set.mem_univ η) a
        (Scheme.Modules.Invertible.stalkGenerator ℒ)
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat η).map a)
        (P.Γgerm η (Scheme.Modules.Invertible.stalkGenerator ℒ)) =
      Q.presheaf.Γgerm η c at hnat
    have hz : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat η).map a)
        (P.Γgerm η (Scheme.Modules.Invertible.stalkGenerator ℒ)) = 0 :=
      hnat.trans (by rw [hzero]; exact map_zero _)
    exact hz.trans
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat η).map a).hom.map_zero).symm
  have hm : m ≠ 0 := by
    intro hzero
    apply hc
    apply (ConcreteCategory.bijective_of_isIso
      (e.inv.hom.app (Opposite.op (⊤ : Opens X.toTopCat)))).1
    change e.inv.hom.app (Opposite.op (⊤ : Opens X.toTopCat)) c =
      e.inv.hom.app (Opposite.op (⊤ : Opens X.toTopCat)) 0
    rw [map_zero]
    exact hzero
  have ht : t ≠ 0 := by
    intro hzero
    apply hm
    have htop := congrArg
      (fun z : G.sections ↦ z.1 (Opposite.op (⊤ : Opens X.toTopCat))) hzero
    have heval := RingedSpace.sectionFromTop_eval_top (X := Y) G m
    have hzeroTop : (0 : G.sections).1
        (Opposite.op (⊤ : Opens X.toTopCat)) = 0 := rfl
    exact heval.symm.trans (htop.trans hzeroTop)
  refine ⟨t, ?_⟩
  apply (isRegularMeromorphicSection_iff_ne_zero_of_isIntegral X ℒ t).2
  exact ht

namespace Scheme.Modules.Invertible

/-- A distinguished regular meromorphic section of an invertible module on an integral scheme. -/
noncomputable def regularMeromorphicSection
    [IsIntegral X] (ℒ : X.Modules) [Invertible ℒ] :
    X.toLocallyRingedSpace.meromorphicSections ℒ :=
  Classical.choose (exists_regularMeromorphicSection_of_isIntegral ℒ)

/-- The distinguished meromorphic section of an invertible module is regular. -/
theorem regularMeromorphicSection_isRegular
    [IsIntegral X] (ℒ : X.Modules) [Invertible ℒ] :
    X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ
      (regularMeromorphicSection ℒ) :=
  Classical.choose_spec (exists_regularMeromorphicSection_of_isIntegral ℒ)

end Scheme.Modules.Invertible

namespace Scheme.Modules.Invertible

/-- An invertible module on a reduced scheme with finitely many irreducible components on each
quasi-compact open has a regular meromorphic section. -/
@[stacks 02OZ "reduced case"]
theorem exists_regularMeromorphicSection_of_isReduced
    [IsReduced X] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s := sorry

end Scheme.Modules.Invertible

/-- An invertible module on a locally Noetherian scheme without embedded points has a regular
meromorphic section. -/
@[stacks 02OZ "locally Noetherian case"]
theorem exists_regularMeromorphicSection_of_isLocallyNoetherian_noEmbeddedPoints
    [IsLocallyNoetherian X]
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    ∃ s : X.toLocallyRingedSpace.meromorphicSections ℒ,
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s := sorry

/-- For an invertible module on an integral scheme, a meromorphic section is regular exactly
when it is nonzero. -/
theorem isRegularMeromorphicSection_iff_ne_zero
    [IsIntegral X] (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) :
    X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s ↔ s ≠ 0 :=
  isRegularMeromorphicSection_iff_ne_zero_of_isIntegral X ℒ s

namespace Scheme.Modules.Invertible

/-- The distinguished regular meromorphic section of an invertible module is nonzero. -/
theorem regularMeromorphicSection_ne_zero
    [IsIntegral X] (ℒ : X.Modules) [Invertible ℒ] :
    regularMeromorphicSection ℒ ≠ 0 :=
  (isRegularMeromorphicSection_iff_ne_zero ℒ (regularMeromorphicSection ℒ)).1
    (regularMeromorphicSection_isRegular ℒ)

end Scheme.Modules.Invertible

/-- The tensor product of two nonzero meromorphic sections of invertible modules on an integral
scheme is nonzero. -/
theorem meromorphicSectionTensor_ne_zero
    [IsIntegral X] {ℒ 𝒩 : X.Modules}
    [Scheme.Modules.Invertible ℒ] [Scheme.Modules.Invertible 𝒩]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (t : X.toLocallyRingedSpace.meromorphicSections 𝒩)
    (hs : s ≠ 0) (ht : t ≠ 0) :
    X.toLocallyRingedSpace.meromorphicSectionTensor s t ≠ 0 :=
  (isRegularMeromorphicSection_iff_ne_zero (ℒ ⊗ 𝒩)
      (X.toLocallyRingedSpace.meromorphicSectionTensor s t)).1
    (@LocallyRingedSpace.isRegularMeromorphicSection_tensor
      X.toLocallyRingedSpace ℒ 𝒩
      Scheme.Modules.Invertible.instRingedSpaceIsInvertible
      Scheme.Modules.Invertible.instRingedSpaceIsInvertible s t
      ((isRegularMeromorphicSection_iff_ne_zero ℒ s).2 hs)
      ((isRegularMeromorphicSection_iff_ne_zero 𝒩 t).2 ht))

end AlgebraicGeometry
