/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import stacks_project.Chap60.Lemma_60_12_2
public import stacks_project.Chap60.Lemma_60_6_3
public import stacks_project.Chap60.Lemma_60_6_5
public import stacks_project.Chap60.Lemma_60_12_3
public import stacks_project.Chap60.Lemma_60_12_4
public import stacks_project.Chap60.Lemma_60_12_5_Diagonal
public import stacks_project.Chap60.«60_9_1_1»

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open DividedPowers
open DividedPowerScheme.RelativeDifferentials
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Lemma 60.12.5 (1): in Situation 60.7.5, for an object `(U, T, δ)` of
`Cris(X/S)` with self-product `(U(1), T(1), δ(1))`, the diagonal ideal sheaf
`𝒦` of `Δ : T → T(1)` is a sub-DP-ideal of `𝒥_{T(1)}`. -/
@[stacks 07J1]
theorem crystallineDifferentials_diagonal_isSubDPIdeal
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T T1 : smallCrystallineSite S I γ h_compatible X x₀)
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (V : T1.obj.1.thickening.affineOpens) :
    IsSubDPIdeal (T1.obj.1.gamma V)
      ((crystallineSiteDiagKer π0 π1 hprod).ideal V ⊓ T1.obj.1.ideal.ideal V) := sorry

/-- The two projections of a self-product cone pull the same opens of `T` back
along the same open of `T(1)`. -/
theorem crystallineSiteDiag_π0_preimage_le_π1
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (U : T.obj.1.thickening.Opens) :
    π0.hom.thickening ⁻¹ᵁ U ≤ π1.hom.thickening ⁻¹ᵁ U := sorry

/-- The difference `π1^*(a) - π0^*(a)` lies in the diagonal kernel ideal. -/
theorem crystallineSiteDiag_diff_mem_sectionIdeal
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U : (T.obj.1.thickening.Opens)ᵒᵖ}
    (a : T.obj.1.thickening.presheaf.obj U) :
    let V : T1.obj.1.thickening.Opens := π0.hom.thickening ⁻¹ᵁ U.unop
    let a0 := π0.hom.thickening.appLE U.unop V le_rfl a
    let a1 := π1.hom.thickening.appLE U.unop V
      (crystallineSiteDiag_π0_preimage_le_π1 π0 π1 hprod U.unop) a
    a1 - a0 ∈
      KernelIdeal.sectionIdeal
        (RingedSpace.Hom.commRingSheafPushforwardMap
          (crystallineSiteDiagKer π0 π1 hprod).subschemeι.toShHom)
        (op V) := sorry

/-- The original open of `T` is contained in the diagonal pullback of the
corresponding open of `T(1)`. -/
theorem crystallineSiteDiag_le_diag_preimage
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (U : T.obj.1.thickening.Opens) :
    U ≤ (crystallineSiteDiag π0 π1 hprod).hom.thickening ⁻¹ᵁ
      (π0.hom.thickening ⁻¹ᵁ U) := sorry

/-- The class of `π1^*(a) - π0^*(a)` in the pullback of `𝒦 / 𝒦^[2]`. -/
noncomputable def crystallineSiteDiagKernelClass
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U : (T.obj.1.thickening.Opens)ᵒᵖ}
    (a : T.obj.1.thickening.presheaf.obj U) :
    ((Scheme.Modules.pullback
        (crystallineSiteDiag π0 π1 hprod).hom.thickening).obj
      (crystallineSiteDiagKernelQuotient π0 π1 hprod)).val.obj U :=
  let Δth := (crystallineSiteDiag π0 π1 hprod).hom.thickening
  let V : T1.obj.1.thickening.Opens := π0.hom.thickening ⁻¹ᵁ U.unop
  let a0 := π0.hom.thickening.appLE U.unop V le_rfl a
  let a1 := π1.hom.thickening.appLE U.unop V
    (crystallineSiteDiag_π0_preimage_le_π1 π0 π1 hprod U.unop) a
  let Kiso := (crystallineSiteDiagKer π0 π1 hprod).toModuleIso
  let Kinv := Kiso.inv
  let Kapp := Kinv.val.app (op V)
  let y :=
    Kapp
      ((KernelIdeal.sectionsIso
          (RingedSpace.Hom.commRingSheafPushforwardMap
            (crystallineSiteDiagKer π0 π1 hprod).subschemeι.toShHom)
          (op V)).inv
        ⟨a1 - a0, crystallineSiteDiag_diff_mem_sectionIdeal π0 π1 hprod a⟩)
  let z :=
    (cokernel.π (crystallineSiteDiagSecondOrder_arrow π0 π1 hprod)).val.app (op V) y
  let zPush :=
    ((Scheme.Modules.pullbackPushforwardAdjunction Δth).unit.app
        (crystallineSiteDiagKernelQuotient π0 π1 hprod)).val.app (op V) z
  let _W : T.obj.1.thickening.Opens := Δth ⁻¹ᵁ V
  ((Scheme.Modules.pullback Δth).obj
      (crystallineSiteDiagKernelQuotient π0 π1 hprod)).val.map
    (homOfLE (crystallineSiteDiag_le_diag_preimage π0 π1 hprod U.unop)).op zPush

/-- The difference of the two projections as an `S`-relative derivation valued in
the pullback of `𝒦 / 𝒦^[2]`. -/
noncomputable def crystallineSiteDiagKernelDerivation
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1)) :
    RingedSpace.Hom.derivations T.obj.1.thickeningToBase.toShHom
      ((Scheme.Modules.pullback
          (crystallineSiteDiag π0 π1 hprod).hom.thickening).obj
        (crystallineSiteDiagKernelQuotient π0 π1 hprod)) where
  d {_U} := AddMonoidHom.mk'
    (fun a ↦ crystallineSiteDiagKernelClass π0 π1 hprod a) sorry
  d_mul := sorry
  d_map := sorry
  d_app := sorry

/-- The divided-power relative differential owner whose underlying module is the
pullback of `𝒦 / 𝒦^[2]`. -/
noncomputable def crystallineSiteDiagKernelRelative
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent) :
    DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase :=
  DividedPowerScheme.RelativeDifferentials.of _ _ _
    ((Scheme.Modules.pullback
        (crystallineSiteDiag π0 π1 hprod).hom.thickening).obj
      (crystallineSiteDiagKernelQuotient π0 π1 hprod))
    (RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
      (crystallineSiteDiagKernelDerivation π0 π1 hprod))
    sorry sorry


/-- The derivation-induced comparison `Ω[T/S] ⟶ Δ^*(𝒦 / 𝒦^[2])` is an isomorphism. -/
instance crystallineSiteDiagKernelDerivation_desc_isIso
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1)) :
    IsIso (RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
      (crystallineSiteDiagKernelDerivation π0 π1 hprod)) := sorry

/-- Lemma 60.12.5 (2): in Situation 60.7.5, the crystalline differentials
`(Ω_{X/S})_T` are identified with the pullback along the diagonal of the
quotient `𝒦 / 𝒦^[2]`. -/
@[stacks 07J1]
noncomputable def crystallineDifferentials_diagonalKernel
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T T1 : smallCrystallineSite S I γ h_compatible X x₀)
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent) :
    Ω_XS.module.obj T.obj.1 ≅
      (Scheme.Modules.pullback (crystallineSiteDiag π0 π1 hprod).hom.thickening).obj
        (crystallineSiteDiagKernelQuotient π0 π1 hprod) :=
  { hom :=
      Ω_XS.comparison T.obj.1 h_T_quasiCoherent
        (crystallineSiteDiagKernelRelative π0 π1 hprod h_T_quasiCoherent)
    inv :=
      (@asIso _ _ _ _
          (RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
            (crystallineSiteDiagKernelDerivation π0 π1 hprod))
          (crystallineSiteDiagKernelDerivation_desc_isIso π0 π1 hprod)).inv ≫
        RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
          (Ω_XS.derivation.component T.obj.1)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The diagonal kernel is contained in the distinguished thickening ideal
`𝒥_{T(1)}`. -/
theorem crystallineDifferentials_diagonalKer_le_ideal
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T T1 : smallCrystallineSite S I γ h_compatible X x₀)
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1)) :
    crystallineSiteDiagKer π0 π1 hprod ≤ T1.obj.1.ideal := sorry

/-- The comparison of Lemma 60.12.5 (2) is an isomorphism, and on affine
opens it agrees with `DividedPowerThickening.kernelComparisonEquiv` after
`crystallineDifferentials_affineSections`. -/
theorem crystallineDifferentials_diagonalKernel_spec
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T T1 : smallCrystallineSite S I γ h_compatible X x₀)
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    [IsAffine T.obj.1.thickening]
    (V : S.affineOpens)
    (hTV : (⊤ : T.obj.1.thickening.Opens) ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V.1) :
    let W : T.obj.1.thickening.affineOpens := ⟨⊤, isAffineOpen_top T.obj.1.thickening⟩
    let iso :=
      crystallineDifferentials_diagonalKernel p S I γ h_compatible
        h_I_quasiCoherent s X x₀ h_p T T1 π0 π1 hprod Ω_XS h_T_quasiCoherent
    ∃ eΩ : Γ(Ω_XS.module.obj T.obj.1, ⊤) ≃ₗ[Γ(T.obj.1.thickening, ⊤)]
        dividedPowerDifferential
          (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W),
      (∀ a : Γ(T.obj.1.thickening, ⊤),
          eΩ (((Ω_XS.derivation.component T.obj.1).app (op ⊤)).d a) =
            dividedPowerDifferentialDerivation
              (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom
              (T.obj.1.gamma W) a) ∧
      ∀ a : Γ(T.obj.1.thickening, ⊤),
        eΩ ((iso.inv.app ⊤)
          (crystallineSiteDiagKernelClass π0 π1 hprod a)) =
          dividedPowerDifferentialDerivation
            (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom
            (T.obj.1.gamma W) a := sorry

/-- Evaluation of the diagonal-kernel comparison on the universal crystalline
derivation: `d_{X/S}(a)` maps to the class of `π1^*(a) - π0^*(a)` in
`𝒦 / 𝒦^[2]`. -/
theorem crystallineDifferentials_diagonalKernel_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T T1 : smallCrystallineSite S I γ h_compatible X x₀)
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (a : Γ(T.obj.1.thickening, ⊤)) :
    ((crystallineDifferentials_diagonalKernel p S I γ h_compatible
          h_I_quasiCoherent s X x₀ h_p T T1 π0 π1 hprod Ω_XS
          h_T_quasiCoherent).hom.app ⊤)
        (((Ω_XS.derivation.component T.obj.1).app (op ⊤)).d a) =
      crystallineSiteDiagKernelClass π0 π1 hprod a := sorry
