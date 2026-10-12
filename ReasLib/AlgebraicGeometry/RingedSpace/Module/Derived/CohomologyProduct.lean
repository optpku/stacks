/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
        (singleFunctorCompHomologyFunctorIso Y.Modules 0).app (𝟙_ Y.Modules) := sorry

/-- The right-hand boundary vanishes when the canonical tensor pairing is passed to cycles. -/
theorem sheafCochainCohomologyProduct_descendsRight
    {Y : RingedSpace.{u}} (K L : CochainComplex Y.Modules ℤ) (p q : ℤ) :
    let f₀ := HomologicalComplex.CohomologyCup.cycles (𝟙 (K ⊗ L)) p q
    let g₀ : L.cycles q ⟶ (ihom (K.cycles p)).obj ((K ⊗ L).homology (p + q)) :=
      MonoidalClosed.curry f₀
    (L.sc q).toCycles ≫ g₀ = 0 := sorry

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
    (K.sc p).toCycles ≫ g₁' = 0 := sorry

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

/-- The complex-level product is induced by the identity pairing on the tensor complex. -/
theorem sheafCochainCohomologyProduct_spec
    {Y : RingedSpace.{u}} (K L : CochainComplex Y.Modules ℤ) (p q : ℤ) :
    HomologicalComplex.CohomologyCup.IsInduced (𝟙 (K ⊗ L)) p q
      (sheafCochainCohomologyProduct K L p q) := sorry

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
        F.objObjPreimageIso E := sorry

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
        (L.objObjPreimageIso E ⊗ᵢ L.objObjPreimageIso F) := sorry

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
          (kFlatComplexPreimageTensorIso E F).hom) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
