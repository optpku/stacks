/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open RingedSpace
open DerivedCategory MonoidalClosed ModuleDerived
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

/-- The derived tensor unit has the expected degree-zero cohomology sheaf. -/
noncomputable def derivedTensorUnitCohomologyIso
    (Y : RingedSpace.{u}) [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y] :
    cohomologySheaf (𝟙_ (ModuleDerived Y)) 0 ≅ 𝟙_ Y.Modules :=
  (homologyFunctor Y.Modules 0).mapIso KFlat.mapUnitIso ≪≫
    (homologyFunctor Y.Modules 0).mapIso
      ((quotientCompQhIso Y.Modules).app
        ((CochainComplex.singleFunctor Y.Modules 0).obj (𝟙_ Y.Modules))) ≪≫
    (singleFunctorCompHomologyFunctorIso Y.Modules 0).app (𝟙_ Y.Modules)

/-- `derivedTensorUnitCohomologyIso` is the composite of the K-flat unit comparison,
the quotient comparison, and degree-zero homology of a single complex. -/
theorem derivedTensorUnitCohomologyIso_def
    (Y : RingedSpace.{u}) [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y] :
    derivedTensorUnitCohomologyIso Y =
      (homologyFunctor Y.Modules 0).mapIso KFlat.mapUnitIso ≪≫
        (homologyFunctor Y.Modules 0).mapIso
          ((quotientCompQhIso Y.Modules).app
            ((CochainComplex.singleFunctor Y.Modules 0).obj (𝟙_ Y.Modules))) ≪≫
        (singleFunctorCompHomologyFunctorIso Y.Modules 0).app (𝟙_ Y.Modules) := by
  rfl

private theorem cohomologyProduct_tensorDifferential
    {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] (K L : CochainComplex C ℤ)
    [HomologicalComplex.HasTensor K L] (p q p' q' r : ℤ)
    (hp : p + 1 = p') (hq : q + 1 = q') (hr : p + q + 1 = r) :
    HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
        (HomologicalComplex.tensorObj K L).d (p + q) r =
      (K.d p p' ⊗ₘ 𝟙 (L.X q)) ≫
          HomologicalComplex.ιTensorObj K L p' q r
            (by rw [← hp, add_right_comm, hr]) +
        p.negOnePow • ((𝟙 (K.X p) ⊗ₘ L.d q q') ≫
          HomologicalComplex.ιTensorObj K L p q' r
            (by rw [← hq, ← add_assoc, hr])) := by
  subst p' q' r
  exact HomologicalComplex.ιTensorObj_d p q

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyProduct_cyclesBoundaryRight
    {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] (K L : CochainComplex C ℤ)
    [HomologicalComplex.HasTensor K L] (p q : ℤ) :
    (𝟙 (K.cycles p) ⊗ₘ (L.sc q).toCycles) ≫
      HomologicalComplex.CohomologyCup.cycles
        (𝟙 (HomologicalComplex.tensorObj K L)) p q = 0 := by
  unfold HomologicalComplex.CohomologyCup.cycles
  erw [← Category.assoc, HomologicalComplex.comp_liftCycles]
  let i := (ComplexShape.up ℤ).prev q
  have hi : i + 1 = q := by
    dsimp [i]
    rw [CochainComplex.prev]
    exact sub_add_cancel q 1
  have hpq : p + i + 1 = p + q := by rw [add_assoc, hi]
  let x := p.negOnePow •
    ((K.iCycles p ⊗ₘ 𝟙 (L.X i)) ≫
      HomologicalComplex.ιTensorObj K L p i (p + i) rfl)
  apply (HomologicalComplex.tensorObj K L).liftCycles_homologyπ_eq_zero_of_boundary _ _ _ x
  have hd := cohomologyProduct_tensorDifferential K L p i (p + 1) q (p + q)
    rfl hi hpq
  have hb : (L.sc q).toCycles ≫ L.iCycles q = L.d i q :=
    (L.sc q).toCycles_i
  dsimp only [x]
  erw [HomologicalComplex.id_f, Category.comp_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp, hb]
  erw [Preadditive.zsmul_comp, Category.assoc, hd,
    Preadditive.comp_add, Preadditive.comp_zsmul,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, HomologicalComplex.iCycles_d,
    Category.comp_id, MonoidalPreadditive.zero_tensor, zero_comp, zero_add,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyProduct_cyclesBoundaryLeft
    {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] (K L : CochainComplex C ℤ)
    [HomologicalComplex.HasTensor K L] (p q : ℤ) :
    ((K.sc p).toCycles ⊗ₘ 𝟙 (L.cycles q)) ≫
      HomologicalComplex.CohomologyCup.cycles
        (𝟙 (HomologicalComplex.tensorObj K L)) p q = 0 := by
  unfold HomologicalComplex.CohomologyCup.cycles
  erw [← Category.assoc, HomologicalComplex.comp_liftCycles]
  let i := (ComplexShape.up ℤ).prev p
  have hi : i + 1 = p := by
    dsimp [i]
    rw [CochainComplex.prev]
    exact sub_add_cancel p 1
  have hpq : i + q + 1 = p + q := by rw [add_right_comm, hi]
  let x := (𝟙 (K.X i) ⊗ₘ L.iCycles q) ≫
    HomologicalComplex.ιTensorObj K L i q (i + q) rfl
  apply (HomologicalComplex.tensorObj K L).liftCycles_homologyπ_eq_zero_of_boundary _ _ _ x
  have hd := cohomologyProduct_tensorDifferential K L i q p (q + 1) (p + q)
    hi rfl hpq
  have hb : (K.sc p).toCycles ≫ K.iCycles p = K.d i p :=
    (K.sc p).toCycles_i
  dsimp only [x]
  erw [HomologicalComplex.id_f, Category.comp_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp, hb]
  erw [Category.assoc, hd, Preadditive.comp_add, Preadditive.comp_zsmul,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id,
    HomologicalComplex.iCycles_d, MonoidalPreadditive.tensor_zero, zero_comp,
    smul_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The right-hand boundary vanishes when the canonical tensor pairing is passed to cycles. -/
theorem sheafCochainCohomologyProduct_descendsRight
    {Y : RingedSpace.{u}} (K L : CochainComplex Y.Modules ℤ) (p q : ℤ) :
    let f₀ := HomologicalComplex.CohomologyCup.cycles (𝟙 (K ⊗ L)) p q
    let g₀ : L.cycles q ⟶ (ihom (K.cycles p)).obj ((K ⊗ L).homology (p + q)) :=
      MonoidalClosed.curry f₀
    (L.sc q).toCycles ≫ g₀ = 0 := by
  dsimp only
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  simp only [MonoidalClosed.uncurry_eq, MonoidalPreadditive.whiskerLeft_zero, zero_comp]
  rw [← MonoidalCategory.id_tensorHom]
  exact cohomologyProduct_cyclesBoundaryRight K L p q

set_option backward.isDefEq.respectTransparency false in
/-- The left-hand boundary vanishes after descending the canonical tensor pairing in the right
variable. -/
theorem sheafCochainCohomologyProduct_descendsLeft
    {Y : RingedSpace.{u}} (K L : CochainComplex Y.Modules ℤ) (p q : ℤ) :
    let f₀ := HomologicalComplex.CohomologyCup.cycles (𝟙 (K ⊗ L)) p q
    let g₀ : L.cycles q ⟶ (ihom (K.cycles p)).obj ((K ⊗ L).homology (p + q)) :=
      MonoidalClosed.curry f₀
    let g₁ : L.homology q ⟶ (ihom (K.cycles p)).obj ((K ⊗ L).homology (p + q)) :=
      (L.sc q).descHomology g₀ (sheafCochainCohomologyProduct_descendsRight K L p q)
    let f₁ : K.cycles p ⊗ L.homology q ⟶ (K ⊗ L).homology (p + q) :=
      MonoidalClosed.uncurry g₁
    let g₁' : K.cycles p ⟶ (ihom (L.homology q)).obj ((K ⊗ L).homology (p + q)) :=
      MonoidalClosed.curry ((β_ (L.homology q) (K.cycles p)).hom ≫ f₁)
    (K.sc p).toCycles ≫ g₁' = 0 := by
  let f₀ := HomologicalComplex.CohomologyCup.cycles (𝟙 (K ⊗ L)) p q
  let g₀ := MonoidalClosed.curry f₀
  let g₁ := (L.sc q).descHomology g₀
    (sheafCochainCohomologyProduct_descendsRight K L p q)
  let f₁ := MonoidalClosed.uncurry g₁
  change (K.sc p).toCycles ≫
    MonoidalClosed.curry ((β_ (L.homology q) (K.cycles p)).hom ≫ f₁) = 0
  have hf₁ : (K.cycles p ◁ L.homologyπ q) ≫ f₁ = f₀ := by
    dsimp only [f₁, g₁]
    rw [← MonoidalClosed.uncurry_natural_left]
    erw [ShortComplex.π_descHomology]
    exact MonoidalClosed.uncurry_curry f₀
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  simp only [MonoidalClosed.uncurry_eq, MonoidalPreadditive.whiskerLeft_zero, zero_comp]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  suffices h : (K.sc p).toCycles ▷ L.homology q ≫ f₁ = 0 by
    rw [h, comp_zero]
  haveI : Epi ((K.sc p).X₁ ◁ L.homologyπ q) :=
    (MonoidalCategory.tensorLeft (K.sc p).X₁).map_epi (L.homologyπ q)
  apply (cancel_epi ((K.sc p).X₁ ◁ L.homologyπ q)).mp
  erw [comp_zero, MonoidalCategory.whisker_exchange_assoc, hf₁]
  rw [← MonoidalCategory.tensorHom_id]
  exact cohomologyProduct_cyclesBoundaryLeft K L p q

/-- The canonical product on the cohomology of two complexes of module sheaves. -/
noncomputable def sheafCochainCohomologyProduct
    {Y : RingedSpace.{u}} (K L : CochainComplex Y.Modules ℤ) (p q : ℤ) :
    K.homology p ⊗ L.homology q ⟶ (K ⊗ L).homology (p + q) :=
  let f₀ := HomologicalComplex.CohomologyCup.cycles (𝟙 (K ⊗ L)) p q
  let g₀ : L.cycles q ⟶ (ihom (K.cycles p)).obj ((K ⊗ L).homology (p + q)) :=
    MonoidalClosed.curry f₀
  let g₁ : L.homology q ⟶ (ihom (K.cycles p)).obj ((K ⊗ L).homology (p + q)) :=
    (L.sc q).descHomology g₀ (sheafCochainCohomologyProduct_descendsRight K L p q)
  let f₁ : K.cycles p ⊗ L.homology q ⟶ (K ⊗ L).homology (p + q) :=
    MonoidalClosed.uncurry g₁
  let g₁' : K.cycles p ⟶ (ihom (L.homology q)).obj ((K ⊗ L).homology (p + q)) :=
    MonoidalClosed.curry ((β_ (L.homology q) (K.cycles p)).hom ≫ f₁)
  let g₂ : K.homology p ⟶ (ihom (L.homology q)).obj ((K ⊗ L).homology (p + q)) :=
    (K.sc p).descHomology g₁'
      (sheafCochainCohomologyProduct_descendsLeft K L p q)
  (β_ (K.homology p) (L.homology q)).hom ≫ MonoidalClosed.uncurry g₂

set_option backward.isDefEq.respectTransparency false in
/-- The complex-level product is induced by the identity pairing on the tensor complex. -/
theorem sheafCochainCohomologyProduct_spec
    {Y : RingedSpace.{u}} (K L : CochainComplex Y.Modules ℤ) (p q : ℤ) :
    HomologicalComplex.CohomologyCup.IsInduced (𝟙 (K ⊗ L)) p q
      (sheafCochainCohomologyProduct K L p q) := by
  dsimp only [HomologicalComplex.CohomologyCup.IsInduced,
    sheafCochainCohomologyProduct]
  erw [BraidedCategory.braiding_naturality_assoc,
    MonoidalCategory.tensorHom_def_assoc,
    ← MonoidalClosed.uncurry_natural_left,
    ShortComplex.π_descHomology, MonoidalClosed.uncurry_curry,
    BraidedCategory.braiding_naturality_left_assoc,
    SymmetricCategory.symmetry_assoc,
    ← MonoidalClosed.uncurry_natural_left,
    ShortComplex.π_descHomology, MonoidalClosed.uncurry_curry]

/-- The K-flat localization is essentially surjective under the selected localization
hypothesis. -/
noncomputable instance kFlatLocalizationEssSurj
    (Y : RingedSpace.{u}) [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y] :
    (KFlat.localizationFunctor :
      HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y).EssSurj :=
  Localization.essSurj
    (KFlat.localizationFunctor :
      HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y)
    HomotopyCategory.KFlat.quasiIso

/-- The canonical comparison from a selected K-flat complex representative to its derived
object. -/
noncomputable def kFlatComplexPreimageIso
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y] (E : ModuleDerived Y) :
    (Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y).obj
        ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).objPreimage
          (((KFlat.localizationFunctor :
            HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y).objPreimage E).obj)) ≅ E :=
  let F : HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y :=
    KFlat.localizationFunctor
  let q := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
  let P := F.objPreimage E
  let K := q.objPreimage P.obj
  ((quotientCompQhIso Y.Modules).app K).symm ≪≫
    (Qh : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤
      ModuleDerived Y).mapIso (q.objObjPreimageIso P.obj) ≪≫
    F.objObjPreimageIso E

/-- `kFlatComplexPreimageIso` is the quotient comparison followed by the chosen K-flat
preimage comparisons. -/
theorem kFlatComplexPreimageIso_def
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y] (E : ModuleDerived Y) :
    let F : HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y :=
      KFlat.localizationFunctor
    let q := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
    let P := F.objPreimage E
    let K := q.objPreimage P.obj
    kFlatComplexPreimageIso E =
      ((quotientCompQhIso Y.Modules).app K).symm ≪≫
        (Qh : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤
          ModuleDerived Y).mapIso (q.objObjPreimageIso P.obj) ≪≫
        F.objObjPreimageIso E := by
  rfl

/-- The K-flat tensor comparison identifies the tensor of the selected complex representatives
with the derived tensor product. -/
noncomputable def kFlatComplexPreimageTensorIso
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y] (E F : ModuleDerived Y) :
    let L : HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y :=
      KFlat.localizationFunctor
    let q := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
    let P := q.objPreimage (L.objPreimage E).obj
    let Q' := q.objPreimage (L.objPreimage F).obj
    (Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y).obj (P ⊗ Q') ≅ E ⊗ F :=
  let L : HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y :=
    KFlat.localizationFunctor
  let q := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
  let PE := L.objPreimage E
  let PF := L.objPreimage F
  let P := q.objPreimage PE.obj
  let Q' := q.objPreimage PF.obj
  ((quotientCompQhIso Y.Modules).app (P ⊗ Q')).symm ≪≫
    (Qh : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤
      ModuleDerived Y).mapIso ((Functor.Monoidal.μIso q P Q').symm) ≪≫
    (Qh : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤
      ModuleDerived Y).mapIso
        ((q.objObjPreimageIso PE.obj) ⊗ᵢ (q.objObjPreimageIso PF.obj)) ≪≫
    (KFlat.mapTensorIso PE PF).symm ≪≫
    (L.objObjPreimageIso E ⊗ᵢ L.objObjPreimageIso F)

/-- `kFlatComplexPreimageTensorIso` is the composite of the quotient, monoidal, K-flat tensor,
and chosen-preimage comparisons. -/
theorem kFlatComplexPreimageTensorIso_def
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y] (E F : ModuleDerived Y) :
    let L : HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y :=
      KFlat.localizationFunctor
    let q := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
    let PE := L.objPreimage E
    let PF := L.objPreimage F
    let P := q.objPreimage PE.obj
    let Q' := q.objPreimage PF.obj
    kFlatComplexPreimageTensorIso E F =
      ((quotientCompQhIso Y.Modules).app (P ⊗ Q')).symm ≪≫
        (Qh : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤
          ModuleDerived Y).mapIso ((Functor.Monoidal.μIso q P Q').symm) ≪≫
        (Qh : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤
          ModuleDerived Y).mapIso
            ((q.objObjPreimageIso PE.obj) ⊗ᵢ (q.objObjPreimageIso PF.obj)) ≪≫
        (KFlat.mapTensorIso PE PF).symm ≪≫
        (L.objObjPreimageIso E ⊗ᵢ L.objObjPreimageIso F) := by
  rfl

/-- The canonical cohomology product on derived module sheaves, transported through the K-flat
tensor comparison. -/
noncomputable def derivedSheafCohomologyProduct
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (E F : ModuleDerived Y) (p q : ℤ) :
    cohomologySheaf E p ⊗ cohomologySheaf F q ⟶ cohomologySheaf (E ⊗ F) (p + q) :=
  let L : HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y :=
    KFlat.localizationFunctor
  let Q' := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
  let E' := Q'.objPreimage (L.objPreimage E).obj
  let F' := Q'.objPreimage (L.objPreimage F).obj
  ((((homologyFunctor Y.Modules p).mapIso
        (kFlatComplexPreimageIso E)).inv ⊗ₘ
      ((homologyFunctor Y.Modules q).mapIso
        (kFlatComplexPreimageIso F)).inv) ≫
    (((homologyFunctorFactors Y.Modules p).hom.app E') ⊗ₘ
      ((homologyFunctorFactors Y.Modules q).hom.app F')) ≫
    sheafCochainCohomologyProduct E' F' p q ≫
    (homologyFunctorFactors Y.Modules (p + q)).inv.app (E' ⊗ F') ≫
    (homologyFunctor Y.Modules (p + q)).map
      (kFlatComplexPreimageTensorIso E F).hom)

/-- `derivedSheafCohomologyProduct` is the complex-level product transported through the chosen
K-flat representatives and their tensor comparison. -/
theorem derivedSheafCohomologyProduct_def
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (E F : ModuleDerived Y) (p q : ℤ) :
    let L : HomotopyCategory.KFlat Y.Modules ⥤ ModuleDerived Y :=
      KFlat.localizationFunctor
    let Q' := HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)
    let E' := Q'.objPreimage (L.objPreimage E).obj
    let F' := Q'.objPreimage (L.objPreimage F).obj
    derivedSheafCohomologyProduct E F p q =
      ((((homologyFunctor Y.Modules p).mapIso
            (kFlatComplexPreimageIso E)).inv ⊗ₘ
          ((homologyFunctor Y.Modules q).mapIso
            (kFlatComplexPreimageIso F)).inv) ≫
        (((homologyFunctorFactors Y.Modules p).hom.app E') ⊗ₘ
          ((homologyFunctorFactors Y.Modules q).hom.app F')) ≫
        sheafCochainCohomologyProduct E' F' p q ≫
        (homologyFunctorFactors Y.Modules (p + q)).inv.app (E' ⊗ F') ≫
        (homologyFunctor Y.Modules (p + q)).map
          (kFlatComplexPreimageTensorIso E F).hom) := by
  rfl

end AlgebraicGeometry.RingedSpace.ModuleDerived
