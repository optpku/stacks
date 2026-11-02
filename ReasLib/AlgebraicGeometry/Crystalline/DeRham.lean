/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.Crystalline.Connection
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Tensor
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections

/-! # De Rham complexes of crystals

The terms are sections of module-sheaf tensors with exterior powers of canonical
divided-power differentials. The differential is induced by the canonical sheaf connection.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf CrystallineModuleSheaf.CrisModuleSheaf
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation
universe u

namespace AlgebraicGeometry.Scheme.Crystalline
variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Normalized divided-power exterior forms on a crystalline thickening. -/
abbrev dividedPowerForm (T : smallCrystallineSite S I γ h_compatible X x₀) (i : ℕ) :=
  SheafOfModules.RingedSite.form T.obj.1.thickening.sheaf
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module i

/-- Pullback of normalized divided-power forms along a crystalline morphism. -/
def dividedPowerOmegaPowerComparison
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :
    (i : ℕ) → (Scheme.Modules.pullback f.hom.thickening).obj (dividedPowerForm U i) ⟶
      dividedPowerForm T i
  | 0 => (Scheme.Modules.pullback f.hom.thickening).map
      (unitIsoTensorUnit (𝒪 := U.obj.1.thickening.sheaf)).hom ≫
      (RingedSpace.Hom.pullbackUnitIso f.hom.thickening.toShHom).hom ≫
      (unitIsoTensorUnit (𝒪 := T.obj.1.thickening.sheaf)).inv
  | 1 => differentialsPullback f
  | n + 2 => schemeModulesExteriorPowerComparison f.hom.thickening
      (differentialsPullback f) (n + 2)

/-- Divided-power form comparisons preserve the identity crystalline morphism. -/
theorem dividedPowerOmegaPower_comparison_id
    (T : smallCrystallineSite S I γ h_compatible X x₀) (i : ℕ) :
    dividedPowerOmegaPowerComparison (𝟙 T) i =
      (Scheme.Modules.pullbackId T.obj.1.thickening).hom.app (dividedPowerForm T i) := sorry

/-- Divided-power form comparisons preserve composition through pullback composition. -/
theorem dividedPowerOmegaPower_comparison_comp
    {T U V : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) (g : U ⟶ V) (i : ℕ) :
    dividedPowerOmegaPowerComparison (f ≫ g) i =
      (Scheme.Modules.pullbackComp f.hom.thickening g.hom.thickening).inv.app (dividedPowerForm V i) ≫
        (Scheme.Modules.pullback f.hom.thickening).map (dividedPowerOmegaPowerComparison g i) ≫
          dividedPowerOmegaPowerComparison f i := sorry

/-- The crystalline assignment of normalized divided-power exterior-form sheaves. -/
def dividedPowerOmegaPower (i : ℕ) : CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := dividedPowerForm T i
  comparison f := dividedPowerOmegaPowerComparison f i
  map_id _ := rfl
  map_comp _ _ := rfl
  comparison_id T := by
    change dividedPowerOmegaPowerComparison (𝟙 T) i = 𝟙 _ ≫ _
    rw [Category.id_comp]
    exact dividedPowerOmegaPower_comparison_id T i
  comparison_comp f g := by
    change dividedPowerOmegaPowerComparison (f ≫ g) i = 𝟙 _ ≫ _ ≫ _ ≫ _
    rw [Category.id_comp]
    exact dividedPowerOmegaPower_comparison_comp f g i

/-- The homomorphism of global section rings induced by a crystalline morphism. -/
def crystalSectionRingHom {T U : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) : sectionRing U →+* sectionRing T :=
  (f.hom.thickening.app ⊤).hom

/-- Pullback of divided-power one-form sections along a crystalline morphism. -/
def crystalOneFormsRestrict {T U : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) : oneForms U →+ oneForms T :=
  (abelianGlobalSections_map f.hom.thickening (differentialsPullback f)).hom

/-- Pullback of normalized divided-power exterior-form sections. -/
def crystalFormRestrict {T U : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) (i : ℕ) :
    Γ(dividedPowerForm U i, ⊤) →+ Γ(dividedPowerForm T i, ⊤) :=
  (abelianGlobalSections_map f.hom.thickening (dividedPowerOmegaPowerComparison f i)).hom

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

variable (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]

/-- The de Rham term presheaf has degree zero equal to the original module assignment;
positive degrees take sections after forming the sheaf tensor and exterior powers. -/
def crystalDeRhamTermPresheaf : (i : ℕ) →
    (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u}
  | 0 => toAbelianPresheaf S I γ h_compatible X x₀ F
  | n + 1 => toAbelianPresheaf S I γ h_compatible X x₀
      (crystallineTensor F (dividedPowerOmegaPower (n + 1)))

/-- Restriction of module-valued divided-power forms along a crystalline morphism. -/
def crystalDeRhamTermRestrict
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) (i : ℕ) :
    (crystalDeRhamTermPresheaf F i).obj (op U) ⟶
      (crystalDeRhamTermPresheaf F i).obj (op T) :=
  (crystalDeRhamTermPresheaf F i).map f.op

omit [IsCrystal F] in
/-- The objects of the de Rham term presheaves are global sections of the specified module sheaves. -/
theorem crystalDeRhamTermPresheaf_obj (i : ℕ)
    (T : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ) :
    (crystalDeRhamTermPresheaf F i).obj T =
      match i with
      | 0 => abelianGlobalSections (F.obj T.unop)
      | n + 1 => abelianGlobalSections
          (moduleTensor (𝒪 := T.unop.obj.1.thickening.sheaf) (F.obj T.unop)
            (dividedPowerForm T.unop (n + 1))) := by cases i <;> rfl

set_option backward.privateInPublic true in
private def crystalDifferentialApp (i : ℕ)
    (T : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ) :
    (crystalDeRhamTermPresheaf F i).obj T ⟶
      (crystalDeRhamTermPresheaf F (i + 1)).obj T :=
  match i with
  | 0 => AddCommGrpCat.ofHom
      (((canonicalConnection F T.unop).hom.val.app (op ⊤)).hom.toAddMonoidHom)
  | n + 1 => AddCommGrpCat.ofHom
      (((SheafOfModules.RingedSite.Connection.differential.{u, u}
        (canonicalConnection F T.unop) (exteriorCalculus T.unop) (n + 1)).val.app
          (op ⊤)).hom.toAddMonoidHom)

set_option backward.privateInPublic true in
/-- The extended canonical connection commutes with restriction in the crystalline site. -/
theorem crystalDeRhamDifferentialPresheaf_naturality (i : ℕ)
    {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U) :
    (crystalDeRhamTermPresheaf F i).map f ≫ crystalDifferentialApp F i U =
      crystalDifferentialApp F i T ≫ (crystalDeRhamTermPresheaf F (i + 1)).map f := sorry


/-- Sheafification of the objectwise de Rham terms of a crystal in modules. -/
def crystalDeRhamTerm
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).obj
    (crystalDeRhamTermPresheaf F i)

omit [IsCrystal F] in
/-- Unfolding of `crystalDeRhamTerm` as sheafification of the objectwise de Rham
term presheaf. -/
theorem crystalDeRhamTerm_eq
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    crystalDeRhamTerm p s h_p F i =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}).obj
        (crystalDeRhamTermPresheaf F i) :=
  rfl

set_option backward.privateInPublic true in
/-- The presheaf differential induced by the canonical connection on each thickening. -/
def crystalDeRhamDifferentialPresheaf (i : ℕ) :
    crystalDeRhamTermPresheaf F i ⟶ crystalDeRhamTermPresheaf F (i + 1) where
  app := crystalDifferentialApp F i
  naturality := fun {T U} f ↦ crystalDeRhamDifferentialPresheaf_naturality F i f

/-- Sheafified de Rham differentials of a crystal in modules. -/
def crystalDeRhamDifferential
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    crystalDeRhamTerm p s h_p F i ⟶ crystalDeRhamTerm p s h_p F (i + 1) :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).map
    (crystalDeRhamDifferentialPresheaf F i)

/-- Unfolding of `crystalDeRhamDifferential` as sheafification of the objectwise
connection differentials. -/
theorem crystalDeRhamDifferential_eq
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    crystalDeRhamDifferential p s h_p F i =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}).map
        (crystalDeRhamDifferentialPresheaf F i) :=
  rfl

/-- Consecutive sheafified de Rham differentials compose to zero. -/
theorem crystalDeRhamDifferential_comp
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    crystalDeRhamDifferential p s h_p F i ≫ crystalDeRhamDifferential p s h_p F (i + 1) = 0 :=
  by
    have h : crystalDeRhamDifferentialPresheaf F i ≫
        crystalDeRhamDifferentialPresheaf F (i + 1) = 0 := by
      apply NatTrans.ext
      funext T
      ext x
      cases i with
      | zero =>
        exact congrArg (fun q => q.val.app (op ⊤) x)
          (canonicalConnection_isIntegrable F T.unop)
      | succ n =>
        exact congrArg (fun q => q.val.app (op ⊤) x)
          (SheafOfModules.RingedSite.Connection.squaresToZero_of_isIntegrable
            (canonicalConnection F T.unop) (exteriorCalculus T.unop)
            (canonicalConnection_isIntegrable F T.unop) (n + 1))
    change (presheafToSheaf _ AddCommGrpCat.{u}).map _ ≫
      (presheafToSheaf _ AddCommGrpCat.{u}).map _ = 0
    rw [← Functor.map_comp, h, Functor.map_zero]

/-- The crystalline de Rham complex of sheaves associated to a crystal in modules, with terms obtained by taking sections of the sheaf tensor
with divided-power exterior forms before sheafification. -/
def crystalDeRhamComplex
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}] :
    CochainComplex
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})
      ℕ :=
  CochainComplex.of (crystalDeRhamTerm p s h_p F) (crystalDeRhamDifferential p s h_p F)
    (crystalDeRhamDifferential_comp p s h_p F)

/-- Degree-`i` object of the crystalline de Rham complex of sheaves. -/
theorem crystalDeRhamComplex_X
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    (crystalDeRhamComplex p s h_p F).X i = crystalDeRhamTerm p s h_p F i :=
  rfl

/-- Degree-zero comparison from the objectwise de Rham term to the abelian
presheaf of `F`. -/
def crystalDeRhamTermPresheaf_zeroMap :
    crystalDeRhamTermPresheaf F 0 ⟶
      toAbelianPresheaf S I γ h_compatible X x₀ F where
  app T :=
    AddCommGrpCat.ofHom (AddMonoidHom.id (sectionModule F T.unop))
  naturality := fun {T U} f => by ext x; rfl

/-- Inverse degree-zero comparison from the abelian presheaf of `F` to the
objectwise de Rham term. -/
def crystalDeRhamTermPresheaf_zeroInv :
    toAbelianPresheaf S I γ h_compatible X x₀ F ⟶
      crystalDeRhamTermPresheaf F 0 where
  app T :=
    AddCommGrpCat.ofHom (AddMonoidHom.id (sectionModule F T.unop))
  naturality := fun {T U} f => by ext x; rfl

/-- Objectwise identification of the degree-zero de Rham term with the abelian
presheaf of `F`. -/
def crystalDeRhamTermPresheaf_iso_toAbelianPresheaf :
    crystalDeRhamTermPresheaf F 0 ≅
      toAbelianPresheaf S I γ h_compatible X x₀ F where
  hom := crystalDeRhamTermPresheaf_zeroMap F
  inv := crystalDeRhamTermPresheaf_zeroInv F
  hom_inv_id := by ext T x; rfl
  inv_hom_id := by ext T x; rfl

/-- Truncation of the crystalline de Rham complex onto `F[0]`. -/
def crystalDeRhamTruncation
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasZeroObject
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})] :
    crystalDeRhamComplex p s h_p F ⟶
      (CochainComplex.single₀
          (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
            AddCommGrpCat.{u})).obj
        (toAbelianSheaf p S I γ h_compatible s X x₀ h_p F) :=
  (CochainComplex.toSingle₀Equiv (crystalDeRhamComplex p s h_p F)
      (toAbelianSheaf p S I γ h_compatible s X x₀ h_p F)).symm
    ((presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        AddCommGrpCat.{u}).map
      (crystalDeRhamTermPresheaf_zeroMap F))

/-- The degree-zero component of the de Rham truncation is the sheafified
degree-zero comparison onto `F`. -/
theorem crystalDeRhamTruncation_f_zero
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasZeroObject
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})] :
    (crystalDeRhamTruncation p s h_p F).f 0 =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}).map
        (crystalDeRhamTermPresheaf_zeroMap F) :=
  by simp [crystalDeRhamTruncation]

/-- Positive-degree components of the de Rham truncation vanish. -/
theorem crystalDeRhamTruncation_f_succ
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasZeroObject
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (n : ℕ) :
    (crystalDeRhamTruncation p s h_p F).f (n + 1) = 0 :=
  by simp [crystalDeRhamTruncation]

/-- Identification of the sheafified degree-zero de Rham term with the underlying
abelian sheaf of `F`. -/
def crystalDeRhamTerm_iso_toAbelianSheaf
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}] :
    crystalDeRhamTerm p s h_p F 0 ≅
      toAbelianSheaf p S I γ h_compatible s X x₀ h_p F :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).mapIso
    (crystalDeRhamTermPresheaf_iso_toAbelianPresheaf F)

omit [IsCrystal F] in
/-- Unfolding of the degree-zero comparison as sheafification of the objectwise
identity. -/
theorem crystalDeRhamTerm_iso_toAbelianSheaf_hom
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}] :
    (crystalDeRhamTerm_iso_toAbelianSheaf p s h_p F).hom =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}).map
        (crystalDeRhamTermPresheaf_zeroMap F) :=
  rfl


variable {h_I_quasiCoherent : I.toModule.IsQuasicoherent}

/-- The fixed comparison from crystalline differentials to canonical divided-power differentials. -/
abbrev crystallineDifferentialComparison
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Ω.comparison T.obj.1
    (CrystallineObject.DividedPowerFirstOrderThickening.ideal_isQuasicoherent T)
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials T)

/-- Sections of the forward canonical divided-power differential comparison. -/
def crystalDifferentialsToOneFormsLinear
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Γ(Ω.module.obj T.obj.1, ⊤) →ₗ[sectionRing T] oneForms T :=
  (crystallineDifferentialComparison p s h_p Ω T).val.app (op ⊤) |>.hom

/-- Sections of the inverse of the fixed divided-power comparison, using its explicit certificate. -/
def crystalOneFormsToDifferentialsLinear
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (hΩ : IsIso (crystallineDifferentialComparison p s h_p Ω T)) :
    oneForms T →ₗ[sectionRing T] Γ(Ω.module.obj T.obj.1, ⊤) :=
  (@inv _ _ _ _ (crystallineDifferentialComparison p s h_p Ω T) hΩ).val.app (op ⊤) |>.hom

/-- The inverse of a certified sheaf comparison is bijective on sections. -/
theorem crystalOneFormsToDifferentialsLinear_bijective
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (hΩ : IsIso (crystallineDifferentialComparison p s h_p Ω T)) :
    Function.Bijective (crystalOneFormsToDifferentialsLinear p s h_p Ω T hΩ) := by
  let e := (@asIso _ _ _ _ (crystallineDifferentialComparison p s h_p Ω T) hΩ).symm
  let e' := (PresheafOfModules.evaluation T.obj.1.thickening.ringCatSheaf.obj (op ⊤)).mapIso
    ((SheafOfModules.forget T.obj.1.thickening.ringCatSheaf).mapIso e)
  exact e'.toLinearEquiv.bijective

/-- The comparison from normalized divided-power forms to crystalline exterior-power sheaves. -/
def crystalFormToOmegaPowerHom
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (hΩ : IsIso (crystallineDifferentialComparison p s h_p Ω T)) (i : ℕ) :
    dividedPowerForm T i ⟶ RingedSpace.ExteriorPower.sheaf (Ω.module.obj T.obj.1) i :=
  (formIso (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module i).hom ≫
    ExteriorPower.map T.obj.1.thickening.sheaf
      (@inv _ _ _ _ (crystallineDifferentialComparison p s h_p Ω T) hΩ) i

/-- The comparison from crystalline exterior-power sheaves to normalized divided-power forms. -/
def crystalOmegaPowerToFormHom
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) (i : ℕ) :
    RingedSpace.ExteriorPower.sheaf (Ω.module.obj T.obj.1) i ⟶ dividedPowerForm T i :=
  ExteriorPower.map T.obj.1.thickening.sheaf
      (crystallineDifferentialComparison p s h_p Ω T) i ≫
    (formIso (CrystallineObject.DividedPowerFirstOrderThickening.differentials T).module i).inv

/-- The form comparison on sections applies the exterior-power comparison before taking sections. -/
def crystalFormToOmegaPowerLinear
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (hΩ : IsIso (crystallineDifferentialComparison p s h_p Ω T)) (i : ℕ) :
    Γ(dividedPowerForm T i, ⊤) →ₗ[sectionRing T]
      Γ(RingedSpace.ExteriorPower.sheaf (Ω.module.obj T.obj.1) i, ⊤) :=
  (crystalFormToOmegaPowerHom p s h_p Ω T hΩ i).val.app (op ⊤) |>.hom

/-- The reverse form comparison on sections is induced by the forward sheaf comparison. -/
def crystalOmegaPowerToFormLinear
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) (i : ℕ) :
    Γ(RingedSpace.ExteriorPower.sheaf (Ω.module.obj T.obj.1) i, ⊤) →ₗ[sectionRing T]
      Γ(dividedPowerForm T i, ⊤) :=
  (crystalOmegaPowerToFormHom p s h_p Ω T i).val.app (op ⊤) |>.hom

set_option backward.privateInPublic true in
private def tensorOmegaPowerHomApp
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) (T : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ) :
    (crystalDeRhamTermPresheaf F i).obj T ⟶
      (toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i)).obj T := by
  cases i with
  | zero => exact False.elim (Nat.not_lt_zero 0 hi)
  | succ n =>
    exact AddCommGrpCat.ofHom
      ((moduleTensorMap (𝟙 (F.obj T.unop))
        (crystalFormToOmegaPowerHom p s h_p Ω T.unop (hΩ T.unop) (n + 1))).val.app
          (op ⊤)).hom.toAddMonoidHom

set_option backward.privateInPublic true in
private def tensorOmegaPowerInvApp
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    {i : ℕ} (hi : 0 < i) (T : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ) :
    (toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i)).obj T ⟶
      (crystalDeRhamTermPresheaf F i).obj T := by
  cases i with
  | zero => exact False.elim (Nat.not_lt_zero 0 hi)
  | succ n =>
    exact AddCommGrpCat.ofHom
      ((moduleTensorMap (𝟙 (F.obj T.unop))
        (crystalOmegaPowerToFormHom p s h_p Ω T.unop (n + 1))).val.app
          (op ⊤)).hom.toAddMonoidHom

set_option backward.privateInPublic true in
/-- The sheaf-induced tensor comparison and its certified inverse are natural on the crystalline site. -/
theorem crystalDeRhamTermPresheaf_tensorOmegaPower_naturality
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) :
    (∀ {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U),
      (crystalDeRhamTermPresheaf F i).map f ≫ tensorOmegaPowerHomApp p s h_p F Ω hΩ hi U =
        tensorOmegaPowerHomApp p s h_p F Ω hΩ hi T ≫
          (toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i)).map f) ∧
    (∀ {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U),
      (toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i)).map f ≫
        tensorOmegaPowerInvApp p s h_p F Ω hi U =
      tensorOmegaPowerInvApp p s h_p F Ω hi T ≫ (crystalDeRhamTermPresheaf F i).map f) := sorry

set_option backward.privateInPublic true in
/-- The positive-degree tensor comparison applies the inverse differential comparison at sheaf level. -/
def crystalDeRhamTermPresheaf_tensorOmegaPowerHom
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTermPresheaf F i ⟶
      toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) where
  app := tensorOmegaPowerHomApp p s h_p F Ω hΩ hi
  naturality := fun {T U} f ↦ (crystalDeRhamTermPresheaf_tensorOmegaPower_naturality p s h_p F Ω hΩ hi).1 f

set_option backward.privateInPublic true in
/-- The reverse positive-degree tensor comparison applies the forward differential comparison at sheaf level. -/
def crystalDeRhamTermPresheaf_tensorOmegaPowerInv
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) :
    toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) ⟶
      crystalDeRhamTermPresheaf F i where
  app := tensorOmegaPowerInvApp p s h_p F Ω hi
  naturality := fun {T U} f ↦ (crystalDeRhamTermPresheaf_tensorOmegaPower_naturality p s h_p F Ω hΩ hi).2 f

/-- The two tensor comparisons compose to the identity on the corrected de Rham term. -/
theorem crystalDeRhamTermPresheaf_tensorOmegaPower_hom_inv_id
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTermPresheaf_tensorOmegaPowerHom p s h_p F Ω hΩ hi ≫
      crystalDeRhamTermPresheaf_tensorOmegaPowerInv p s h_p F Ω hΩ hi = 𝟙 _ := by
  apply NatTrans.ext
  funext T
  cases i with
  | zero => exact False.elim (Nat.not_lt_zero 0 hi)
  | succ n =>
    let e := formIso
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T.unop).module (n + 1) ≪≫
      (ExteriorPower.functor T.unop.obj.1.thickening.sheaf (n + 1)).mapIso
        (@asIso _ _ _ _ (crystallineDifferentialComparison p s h_p Ω T.unop) (hΩ T.unop)).symm
    have htensor :
        moduleTensorMap (𝒪 := T.unop.obj.1.thickening.sheaf) (𝟙 (F.obj T.unop))
            (crystalFormToOmegaPowerHom p s h_p Ω T.unop (hΩ T.unop) (n + 1)) ≫
          moduleTensorMap (𝒪 := T.unop.obj.1.thickening.sheaf) (𝟙 (F.obj T.unop))
            (crystalOmegaPowerToFormHom p s h_p Ω T.unop (n + 1)) = 𝟙 _ :=
      (MonoidalCategory.tensorIso (Iso.refl (F.obj T.unop)) e).hom_inv_id
    ext x
    exact congrArg (fun q => q.val.app (op ⊤) x) htensor

/-- The two tensor comparisons compose to the identity on the crystalline tensor coefficient. -/
theorem crystalDeRhamTermPresheaf_tensorOmegaPower_inv_hom_id
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTermPresheaf_tensorOmegaPowerInv p s h_p F Ω hΩ hi ≫
      crystalDeRhamTermPresheaf_tensorOmegaPowerHom p s h_p F Ω hΩ hi = 𝟙 _ := by
  apply NatTrans.ext
  funext T
  cases i with
  | zero => exact False.elim (Nat.not_lt_zero 0 hi)
  | succ n =>
    let e := formIso
      (CrystallineObject.DividedPowerFirstOrderThickening.differentials T.unop).module (n + 1) ≪≫
      (ExteriorPower.functor T.unop.obj.1.thickening.sheaf (n + 1)).mapIso
        (@asIso _ _ _ _ (crystallineDifferentialComparison p s h_p Ω T.unop) (hΩ T.unop)).symm
    have htensor :
        moduleTensorMap (𝒪 := T.unop.obj.1.thickening.sheaf) (𝟙 (F.obj T.unop))
            (crystalOmegaPowerToFormHom p s h_p Ω T.unop (n + 1)) ≫
          moduleTensorMap (𝒪 := T.unop.obj.1.thickening.sheaf) (𝟙 (F.obj T.unop))
            (crystalFormToOmegaPowerHom p s h_p Ω T.unop (hΩ T.unop) (n + 1)) = 𝟙 _ :=
      (MonoidalCategory.tensorIso (Iso.refl (F.obj T.unop)) e).inv_hom_id
    ext x
    exact congrArg (fun q => q.val.app (op ⊤) x) htensor

/-- Positive-degree de Rham terms are canonically the sheaf tensor coefficients of crystalline differentials. -/
def crystalDeRhamTermPresheaf_iso_tensorOmegaPower
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTermPresheaf F i ≅
      toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) where
  hom := crystalDeRhamTermPresheaf_tensorOmegaPowerHom p s h_p F Ω hΩ hi
  inv := crystalDeRhamTermPresheaf_tensorOmegaPowerInv p s h_p F Ω hΩ hi
  hom_inv_id := crystalDeRhamTermPresheaf_tensorOmegaPower_hom_inv_id p s h_p F Ω hΩ hi
  inv_hom_id := crystalDeRhamTermPresheaf_tensorOmegaPower_inv_hom_id p s h_p F Ω hΩ hi

/-- Sheafification of the positive-degree canonical tensor comparison. -/
def crystalDeRhamTerm_iso_tensorOmegaPower
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : ∀ T, IsIso (crystallineDifferentialComparison p s h_p Ω T))
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTerm p s h_p F i ≅
      toAbelianSheaf p S I γ h_compatible s X x₀ h_p (crystallineTensorOmegaPower F Ω i) :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).mapIso
    (crystalDeRhamTermPresheaf_iso_tensorOmegaPower p s h_p F Ω hΩ hi)

end AlgebraicGeometry.Scheme.Crystalline
