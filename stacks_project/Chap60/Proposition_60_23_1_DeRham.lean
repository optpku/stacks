module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars
public import stacks_project.Chap60.Lemma_60_15_1_Connection
public import stacks_project.Chap60.Lemma_60_18_2
public import stacks_project.Chap60.Lemma_60_21_2_OmegaTensor
public import stacks_project.Chap60.Proposition_60_17_4_Categories

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf
open CrisModuleSheaf
open scoped AlgebraicGeometry RelativeDerivation TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (p : ℕ) [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (F : CrisModuleSheaf S I γ h_compatible X x₀)
variable [IsQuasiCoherentCrystal F]

/-- Ring homomorphism on global sections of thickenings along a morphism in the
opposite small crystalline site. -/
def crystalSectionRingHom
    {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U) :
    sectionRing T.unop →+* sectionRing U.unop :=
  (smallCrystallineHom_thickening S I γ h_compatible X x₀ f.unop).app ⊤ |>.hom

/-- Additive restriction of one-forms along a morphism in the opposite small
crystalline site, obtained from functoriality of algebraic Kähler differentials. -/
def crystalOneFormsRestrict
    {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U) :
    oneForms T.unop →+ oneForms U.unop :=
  -- Local instance justification (noncanonical choice): Algebra and scalar tower
  -- along the thickening ring map of `f`, not a global tower on section rings.
  have : Algebra (sectionRing T.unop) (sectionRing U.unop) :=
    (crystalSectionRingHom f).toAlgebra
  have : IsScalarTower Γ(S, ⊤) (sectionRing T.unop) (sectionRing U.unop) := sorry
  have : SMulCommClass Γ(S, ⊤) (sectionRing T.unop) (sectionRing U.unop) := sorry
  (kaehlerToOneFormsEquiv U.unop).toAddMonoidHom.comp
    ((KaehlerDifferential.map Γ(S, ⊤) Γ(S, ⊤)
        (sectionRing T.unop) (sectionRing U.unop)).toAddMonoidHom.comp
      (kaehlerToOneFormsEquiv T.unop).symm.toAddMonoidHom)

/-- Additive restriction of exterior powers along a ring homomorphism. -/
def crystalExteriorPowerRestrict
    {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (n : ℕ) (fMN : M →+ N) :
    ⋀[R]^n M →+ ⋀[S]^n N :=
  -- Local instance justification (noncanonical choice): the algebra structure is
  -- the supplied ring homomorphism of a specific crystalline thickening, not a
  -- global scalar-tower instance.
  have : Algebra R S := σ.toAlgebra
  (RestrictScalars.addEquiv R S (⋀[S]^n N)).toAddMonoidHom.comp
    (LinearMap.toAddMonoidHom
      (exteriorPower.RestrictScalars.map n
        { toFun := fun m => (RestrictScalars.addEquiv R S N).symm (fMN m)
          map_add' := sorry
          map_smul' := sorry }))

/-- Additive restriction of exterior-form terms along a morphism in the opposite
small crystalline site. -/
def crystalFormRestrict
    {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U) :
    (i : ℕ) →
      exteriorPower.form (sectionRing T.unop) (oneForms T.unop) i →+
        exteriorPower.form (sectionRing U.unop) (oneForms U.unop) i
  | 0 => (crystalSectionRingHom f).toAddMonoidHom
  | 1 => crystalOneFormsRestrict f
  | n + 2 =>
      crystalExteriorPowerRestrict (crystalSectionRingHom f) (n + 2)
        (crystalOneFormsRestrict f)

/-- Additive restriction of global sections of `F` along a morphism in the opposite
small crystalline site. -/
def crystalSectionRestrict
    {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U) :
    sectionModule F T.unop →+ sectionModule F U.unop :=
  ((toAbelianPresheaf S I γ h_compatible X x₀ F).map f).hom

/-- Restriction of objectwise de Rham terms along a morphism in the opposite small
crystalline site. -/
def crystalDeRhamTermRestrict
    {T U : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ} (f : T ⟶ U) :
    (i : ℕ) →
      Connection.deRhamTerm (canonicalConnection F T.unop) i ⟶
        Connection.deRhamTerm (canonicalConnection F U.unop) i
  | 0 =>
      AddCommGrpCat.ofHom (crystalSectionRestrict F f)
  | n + 1 =>
      AddCommGrpCat.ofHom
        (TensorProduct.liftAddHom
          { toFun := fun m =>
              { toFun := fun ω =>
                  crystalSectionRestrict F f m ⊗ₜ[sectionRing U.unop]
                    crystalFormRestrict f (n + 1) ω
                map_zero' := sorry
                map_add' := sorry }
            map_zero' := sorry
            map_add' := sorry }
          (fun _ _ _ => sorry))

/-- Objectwise de Rham terms of the canonical crystal connection, as an abelian
presheaf on `Cris(X/S)`. Degree `0` is global sections of `F`; degree `i + 1` is
`F_T ⊗ Λ^{i+1} Ω[T/S]`. -/
def crystalDeRhamTermPresheaf (i : ℕ) :
    (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := Connection.deRhamTerm (canonicalConnection F T.unop) i
  map f := crystalDeRhamTermRestrict F f i
  map_id := sorry
  map_comp := sorry

/-- Unfolding of objectwise de Rham term presheaves. -/
theorem crystalDeRhamTermPresheaf_obj (i : ℕ)
    (T : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ) :
    (crystalDeRhamTermPresheaf F i).obj T =
      Connection.deRhamTerm (canonicalConnection F T.unop) i :=
  sorry

/-- Sheafification of the objectwise de Rham terms of a crystal in quasi-coherent
modules. -/
def crystalDeRhamTerm
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).obj
    (crystalDeRhamTermPresheaf F i)

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
  sorry

/-- Objectwise de Rham differentials of the canonical crystal connection. -/
def crystalDeRhamDifferentialPresheaf (i : ℕ) :
    crystalDeRhamTermPresheaf F i ⟶ crystalDeRhamTermPresheaf F (i + 1) where
  app T :=
    Connection.deRhamDifferential (canonicalConnection F T.unop)
      (exteriorCalculus T.unop) i
  naturality := fun _ _ _ => sorry

/-- Sheafified de Rham differentials of a crystal in quasi-coherent modules. -/
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
  sorry

/-- Consecutive sheafified de Rham differentials compose to zero. -/
theorem crystalDeRhamDifferential_comp
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    (i : ℕ) :
    crystalDeRhamDifferential p s h_p F i ≫ crystalDeRhamDifferential p s h_p F (i + 1) = 0 :=
  sorry

/-- The crystalline de Rham complex of sheaves associated to a crystal in
quasi-coherent modules, with terms `F`, `F ⊗ Ω¹_{X/S}`, `F ⊗ Ω²_{X/S}`, … at the
level of objectwise global sections. -/
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
  sorry

/-- Degree-zero comparison from the objectwise de Rham term to the abelian
presheaf of `F`. -/
def crystalDeRhamTermPresheaf_zeroMap :
    crystalDeRhamTermPresheaf F 0 ⟶
      toAbelianPresheaf S I γ h_compatible X x₀ F where
  app T :=
    AddCommGrpCat.ofHom (AddMonoidHom.id (sectionModule F T.unop))
  naturality := fun _ _ _ => sorry

/-- Inverse degree-zero comparison from the abelian presheaf of `F` to the
objectwise de Rham term. -/
def crystalDeRhamTermPresheaf_zeroInv :
    toAbelianPresheaf S I γ h_compatible X x₀ F ⟶
      crystalDeRhamTermPresheaf F 0 where
  app T :=
    AddCommGrpCat.ofHom (AddMonoidHom.id (sectionModule F T.unop))
  naturality := fun _ _ _ => sorry

/-- Objectwise identification of the degree-zero de Rham term with the abelian
presheaf of `F`. -/
def crystalDeRhamTermPresheaf_iso_toAbelianPresheaf :
    crystalDeRhamTermPresheaf F 0 ≅
      toAbelianPresheaf S I γ h_compatible X x₀ F where
  hom := crystalDeRhamTermPresheaf_zeroMap F
  inv := crystalDeRhamTermPresheaf_zeroInv F
  hom_inv_id := sorry
  inv_hom_id := sorry

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
  sorry

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
  sorry

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

/-- Unfolding of the degree-zero comparison as sheafification of the objectwise
identity. -/
theorem crystalDeRhamTerm_iso_toAbelianSheaf_hom
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}] :
    (crystalDeRhamTerm_iso_toAbelianSheaf p s h_p F).hom =
      (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          AddCommGrpCat.{u}).map
        (crystalDeRhamTermPresheaf_zeroMap F) :=
  sorry

/-- Global sections of crystalline differentials as a module over the thickening
section ring. -/
noncomputable instance crystallineDifferentialsSectionsModule
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Module (sectionRing T) Γ(Ω.module.obj T.obj.1, ⊤) :=
  inferInstanceAs
    (Module Γ(T.obj.1.thickening, ⊤) Γ(Ω.module.obj T.obj.1, ⊤))

/-- Linear map on global one-forms induced by the universal derivation of a
crystalline differentials sheaf. -/
def crystalOneFormsToDifferentialsLinear
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    oneForms T →ₗ[sectionRing T] Γ(Ω.module.obj T.obj.1, ⊤) where
  toFun :=
    (Modules.Hom.app
      (RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
        (Ω.derivation.component T.obj.1))
      ⊤).hom
  map_add' := sorry
  map_smul' := sorry

/-- The universal-derivation comparison on global one-forms is bijective. -/
theorem crystalOneFormsToDifferentialsLinear_bijective
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Function.Bijective (crystalOneFormsToDifferentialsLinear p s h_p Ω T) :=
  sorry

/-- Inverse linear map on global sections of crystalline differentials. -/
def crystalDifferentialsToOneFormsLinear
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Γ(Ω.module.obj T.obj.1, ⊤) →ₗ[sectionRing T] oneForms T :=
  (LinearEquiv.ofBijective (crystalOneFormsToDifferentialsLinear p s h_p Ω T)
      (crystalOneFormsToDifferentialsLinear_bijective p s h_p Ω T)).symm.toLinearMap

/-- Comparison from objectwise exterior forms to global sections of `Ω^i_{X/S}`. -/
def crystalFormToOmegaPowerLinear
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (i : ℕ) →
      exteriorPower.form (sectionRing T) (oneForms T) i →ₗ[sectionRing T]
        ⋀[sectionRing T]^i Γ(Ω.module.obj T.obj.1, ⊤)
  | 0 => 0
  | 1 =>
      (exteriorPower.oneEquiv (R := sectionRing T)
          (M := Γ(Ω.module.obj T.obj.1, ⊤))).symm.toLinearMap.comp
        (crystalOneFormsToDifferentialsLinear p s h_p Ω T)
  | n + 2 =>
      exteriorPower.map (n + 2) (crystalOneFormsToDifferentialsLinear p s h_p Ω T)

/-- Inverse comparison from global sections of `Ω^i_{X/S}` to objectwise exterior
forms. -/
def crystalOmegaPowerToFormLinear
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (i : ℕ) →
      ⋀[sectionRing T]^i Γ(Ω.module.obj T.obj.1, ⊤) →ₗ[sectionRing T]
        exteriorPower.form (sectionRing T) (oneForms T) i
  | 0 => 0
  | 1 =>
      (crystalDifferentialsToOneFormsLinear p s h_p Ω T).comp
        (exteriorPower.oneEquiv (R := sectionRing T)
          (M := Γ(Ω.module.obj T.obj.1, ⊤))).toLinearMap
  | n + 2 =>
      exteriorPower.map (n + 2) (crystalDifferentialsToOneFormsLinear p s h_p Ω T)

/-- Objectwise comparison from de Rham terms to global sections of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`. -/
def crystalDeRhamTermPresheaf_tensorOmegaPowerHom
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTermPresheaf F i ⟶
      toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) where
  app T :=
    match i, hi with
    | 0, h => False.elim (Nat.not_lt_zero 0 h)
    | n + 1, _ =>
        AddCommGrpCat.ofHom
          (LinearMap.toAddMonoidHom
            (TensorProduct.map
              (LinearMap.id (R := sectionRing T.unop) (M := sectionModule F T.unop))
              (crystalFormToOmegaPowerLinear p s h_p Ω T.unop (n + 1))))
  naturality := fun _ _ _ => sorry

/-- Inverse objectwise comparison from global sections of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to de Rham terms. -/
def crystalDeRhamTermPresheaf_tensorOmegaPowerInv
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    {i : ℕ} (hi : 0 < i) :
    toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) ⟶
      crystalDeRhamTermPresheaf F i where
  app T :=
    match i, hi with
    | 0, h => False.elim (Nat.not_lt_zero 0 h)
    | n + 1, _ =>
        AddCommGrpCat.ofHom
          (LinearMap.toAddMonoidHom
            (TensorProduct.map
              (LinearMap.id (R := sectionRing T.unop) (M := sectionModule F T.unop))
              (crystalOmegaPowerToFormLinear p s h_p Ω T.unop (n + 1))))
  naturality := fun _ _ _ => sorry

/-- Objectwise identification of positive-degree de Rham terms with global
sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`. -/
def crystalDeRhamTermPresheaf_iso_tensorOmegaPower
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTermPresheaf F i ≅
      toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) where
  hom := crystalDeRhamTermPresheaf_tensorOmegaPowerHom p s h_p F Ω hi
  inv := crystalDeRhamTermPresheaf_tensorOmegaPowerInv p s h_p F Ω hi
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification of a positive-degree sheafified de Rham term with the
underlying abelian sheaf of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`. -/
def crystalDeRhamTerm_iso_tensorOmegaPower
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    {i : ℕ} (hi : 0 < i) :
    crystalDeRhamTerm p s h_p F i ≅
      toAbelianSheaf p S I γ h_compatible s X x₀ h_p (crystallineTensorOmegaPower F Ω i) :=
  (presheafToSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}).mapIso
    (crystalDeRhamTermPresheaf_iso_tensorOmegaPower p s h_p F Ω hi)

end AlgebraicGeometry.Scheme.Crystalline
