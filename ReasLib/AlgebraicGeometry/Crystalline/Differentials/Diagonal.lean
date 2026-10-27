/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Diagonal
public import ReasLib.AlgebraicGeometry.Crystalline.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf DividedPowers DividedPowerScheme.RelativeDifferentials
open KaehlerDifferential.DeRham
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

universe u

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

namespace AlgebraicGeometry.Scheme.Crystalline.Diagonal

-- Export this private proof dependency for use in exposed data definitions.
set_option backward.privateInPublic true in
/-- The two projections of a self-product cone pull the same opens of `T` back
along the same open of `T(1)`. -/
private theorem preimage_le
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (U : T.obj.1.thickening.Opens) :
    π0.hom.thickening ⁻¹ᵁ U ≤ π1.hom.thickening ⁻¹ᵁ U := sorry

-- Export this private proof dependency for use in exposed data definitions.
set_option backward.privateInPublic true in
/-- The difference `π1^*(a) - π0^*(a)` lies in the diagonal kernel ideal. -/
private theorem diff_mem_sectionIdeal
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U : (T.obj.1.thickening.Opens)ᵒᵖ}
    (a : T.obj.1.thickening.presheaf.obj U) :
    let V : T1.obj.1.thickening.Opens := π0.hom.thickening ⁻¹ᵁ U.unop
    let a0 := π0.hom.thickening.appLE U.unop V le_rfl a
    let a1 := π1.hom.thickening.appLE U.unop V
      (preimage_le π0 π1 hprod U.unop) a
    a1 - a0 ∈
      KernelIdeal.sectionIdeal
        (RingedSpace.Hom.commRingSheafPushforwardMap
          (ideal π0 π1 hprod).subschemeι.toShHom)
        (op V) := sorry

-- Export this private proof dependency for use in exposed data definitions.
set_option backward.privateInPublic true in
/-- The original open of `T` is contained in the diagonal pullback of the
corresponding open of `T(1)`. -/
private theorem le_diag_preimage
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    (U : T.obj.1.thickening.Opens) :
    U ≤ (diag π0 π1 hprod).hom.thickening ⁻¹ᵁ
      (π0.hom.thickening ⁻¹ᵁ U) := sorry

-- Private proof lemmas supply only erased laws in this exposed data definition.
set_option backward.privateInPublic true in
/-- The class of `π1^*(a) - π0^*(a)` in the pullback of `𝒦 / 𝒦^[2]`. -/
noncomputable def differenceClass
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U : (T.obj.1.thickening.Opens)ᵒᵖ}
    (a : T.obj.1.thickening.presheaf.obj U) :
    ((Scheme.Modules.pullback
        (diag π0 π1 hprod).hom.thickening).obj
      (quotient π0 π1 hprod)).val.obj U :=
  let Δth := (diag π0 π1 hprod).hom.thickening
  let V : T1.obj.1.thickening.Opens := π0.hom.thickening ⁻¹ᵁ U.unop
  let a0 := π0.hom.thickening.appLE U.unop V le_rfl a
  let a1 := π1.hom.thickening.appLE U.unop V
    (preimage_le π0 π1 hprod U.unop) a
  let Kiso := (ideal π0 π1 hprod).toModuleIso
  let Kinv := Kiso.inv
  let Kapp := Kinv.val.app (op V)
  let y :=
    Kapp
      ((KernelIdeal.sectionsIso
          (RingedSpace.Hom.commRingSheafPushforwardMap
            (ideal π0 π1 hprod).subschemeι.toShHom)
          (op V)).inv
        ⟨a1 - a0, (diff_mem_sectionIdeal π0 π1 hprod a)⟩)
  let z :=
    (cokernel.π (secondOrderInclusion π0 π1 hprod)).val.app (op V) y
  let zPush :=
    ((Scheme.Modules.pullbackPushforwardAdjunction Δth).unit.app
        (quotient π0 π1 hprod)).val.app (op V) z
  ((Scheme.Modules.pullback Δth).obj
      (quotient π0 π1 hprod)).val.map
    (homOfLE (le_diag_preimage π0 π1 hprod U.unop)).op zPush

-- Export this private proof dependency for use in exposed data definitions.
set_option backward.privateInPublic true in
/-- Difference classes are additive on sections. -/
private theorem differenceClass_add
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U : (T.obj.1.thickening.Opens)ᵒᵖ} (a b : T.obj.1.thickening.presheaf.obj U) :
    differenceClass π0 π1 hprod (a + b) =
      differenceClass π0 π1 hprod a + differenceClass π0 π1 hprod b := sorry

-- Export this private proof dependency for use in exposed data definitions.
set_option backward.privateInPublic true in
/-- Difference classes satisfy the Leibniz rule. -/
private theorem derivation_mul
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U : (T.obj.1.thickening.Opens)ᵒᵖ} (a b : T.obj.1.thickening.presheaf.obj U) :
    differenceClass π0 π1 hprod (a * b) =
      a • differenceClass π0 π1 hprod b + b • differenceClass π0 π1 hprod a := sorry

-- Export this private proof dependency for use in exposed data definitions.
set_option backward.privateInPublic true in
/-- Difference classes commute with restriction of sections. -/
private theorem derivation_map
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U V : (T.obj.1.thickening.Opens)ᵒᵖ} (ρ : U ⟶ V)
    (a : T.obj.1.thickening.presheaf.obj U) :
    differenceClass π0 π1 hprod (T.obj.1.thickening.presheaf.map ρ a) =
      ((Scheme.Modules.pullback (diag π0 π1 hprod).hom.thickening).obj
        (quotient π0 π1 hprod)).val.map ρ (differenceClass π0 π1 hprod a) := sorry

-- Export this private proof dependency for use in exposed data definitions.
set_option backward.privateInPublic true in
/-- Difference classes vanish on sections coming from the base. -/
private theorem derivation_app
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1))
    {U : (T.obj.1.thickening.Opens)ᵒᵖ}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u}
      T.obj.1.thickeningToBase.toShHom.hom.base).obj S.sheaf).obj.obj U) :
    differenceClass π0 π1 hprod
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm
        T.obj.1.thickeningToBase.toShHom).hom.app U a) = 0 := sorry

-- Private proof lemmas supply only erased laws in this exposed data definition.
set_option backward.privateInPublic true in
/-- The difference of the projections is a relative derivation into the diagonal
pullback of the divided-power conormal module. -/
noncomputable def derivation
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1)) :
    RingedSpace.Hom.derivations T.obj.1.thickeningToBase.toShHom
      ((Scheme.Modules.pullback (diag π0 π1 hprod).hom.thickening).obj
        (quotient π0 π1 hprod)) where
  d {_U} := AddMonoidHom.mk' (fun a ↦ differenceClass π0 π1 hprod a)
    (differenceClass_add π0 π1 hprod)
  d_mul := derivation_mul π0 π1 hprod
  d_map := derivation_map π0 π1 hprod
  d_app := derivation_app π0 π1 hprod

/-- The derivation induced by the conormal quotient satisfies the divided-power relation. -/
theorem relative_isDividedPower
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1)) :
    DividedPowerScheme.RelativeDifferentials.IsDividedPower
      (CrystallineObject.toDividedPowerScheme T.obj.1
        (T.obj.1.ideal.toModule_isQuasicoherent)) S T.obj.1.thickeningToBase
      ((d[T.obj.1.thickeningToBase.toShHom]).postcomp
        (RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
          (derivation π0 π1 hprod)).val) := sorry

/-- The diagonal conormal quotient represents divided-power-compatible relative derivations. -/
theorem relative_universal
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1)) :
    ∀ (M : T.obj.1.thickening.Modules)
      (D : DividedPowerScheme.RelativeDifferentials.Derivation
        (CrystallineObject.toDividedPowerScheme T.obj.1
          (T.obj.1.ideal.toModule_isQuasicoherent)) S T.obj.1.thickeningToBase M),
      ∃! q : ((Scheme.Modules.pullback (diag π0 π1 hprod).hom.thickening).obj
        (quotient π0 π1 hprod)) ⟶ M,
        (d[T.obj.1.thickeningToBase.toShHom]).postcomp
          (RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
            (derivation π0 π1 hprod) ≫ q).val = D.toDerivation := sorry

/-- The diagonal conormal module, pulled back along the diagonal, is an explicit
owner of divided-power relative differentials. -/
noncomputable def relativeDifferentials
    {T T1 : smallCrystallineSite S I γ h_compatible X x₀}
    (π0 π1 : T1 ⟶ T) (hprod : IsLimit (BinaryFan.mk π0 π1)) :
    DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1
        (T.obj.1.ideal.toModule_isQuasicoherent)) S T.obj.1.thickeningToBase :=
  DividedPowerScheme.RelativeDifferentials.of _ _ _
    ((Scheme.Modules.pullback (diag π0 π1 hprod).hom.thickening).obj
        (quotient π0 π1 hprod))
    (RingedSpace.Hom.differentialDesc T.obj.1.thickeningToBase.toShHom
      (derivation π0 π1 hprod))
    (relative_isDividedPower π0 π1 hprod) (relative_universal π0 π1 hprod)

end AlgebraicGeometry.Scheme.Crystalline.Diagonal

open AlgebraicGeometry.Scheme.Crystalline.Diagonal

/-- Crystalline differentials are canonically isomorphic to the diagonal pullback
of the divided-power conormal module. -/
noncomputable def CrystallineDifferentials.diagonalKernel
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
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p) :
    Ω_XS.module.obj T.obj.1 ≅
      (Scheme.Modules.pullback (diag π0 π1 hprod).hom.thickening).obj
        (quotient π0 π1 hprod) :=
  @asIso _ _ _ _
    (Ω_XS.comparison T.obj.1 (T.obj.1.ideal.toModule_isQuasicoherent)
      (relativeDifferentials π0 π1 hprod))
    (CrystallineDifferentials.comparison_isIso p S I γ h_compatible
      h_I_quasiCoherent s X x₀ h_p T (T.obj.1.ideal.toModule_isQuasicoherent)
      Ω_XS (relativeDifferentials π0 π1 hprod))

/-- On an affine crystalline thickening, the diagonal comparison identifies difference
classes with the universal ring-level divided-power differential, compatibly with the
affine description of crystalline differentials. -/
theorem CrystallineDifferentials.diagonalKernel_spec
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
    [IsAffine T.obj.1.thickening]
    (V : S.affineOpens)
    (hTV : (⊤ : T.obj.1.thickening.Opens) ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V.1) :
    let W : T.obj.1.thickening.affineOpens := ⟨⊤, isAffineOpen_top T.obj.1.thickening⟩
    let iso :=
      CrystallineDifferentials.diagonalKernel p S I γ h_compatible
        h_I_quasiCoherent s X x₀ h_p T T1 π0 π1 hprod Ω_XS
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
          (differenceClass π0 π1 hprod a)) =
          dividedPowerDifferentialDerivation
            (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom
            (T.obj.1.gamma W) a := sorry

/-- Evaluation of the diagonal-kernel comparison on the universal crystalline
derivation: `d_{X/S}(a)` maps to the class of `π1^*(a) - π0^*(a)` in
`𝒦 / 𝒦^[2]`. -/
theorem CrystallineDifferentials.diagonalKernel_apply
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
    (a : Γ(T.obj.1.thickening, ⊤)) :
    ((CrystallineDifferentials.diagonalKernel p S I γ h_compatible
          h_I_quasiCoherent s X x₀ h_p T T1 π0 π1 hprod Ω_XS).hom.app ⊤)
        (((Ω_XS.derivation.component T.obj.1).app (op ⊤)).d a) =
      differenceClass π0 π1 hprod a := sorry
