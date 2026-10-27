/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Derivation
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.DividedPower
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

universe u

/-- The divided-power scheme carried by a crystalline thickening with a chosen
quasi-coherence proof for its ideal sheaf. -/
def CrystallineObject.toDividedPowerScheme
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (T : CRIS S I γ h_compatible X x₀)
    (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent) :
    DividedPowerScheme :=
  { scheme := T.thickening
    ideal := T.ideal
    quasiCoherent := h_quasiCoherent
    dividedPowers := T.gamma
    compatible := T.thickening_compatible }

/-- The universal crystalline differential sheaf, its `S`-derivation, and the
explicit comparison morphisms to divided-power relative differentials. -/
structure CrystallineDifferentials.{u_1}
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u_1}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u_1} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u_1}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) where
  /-- The crystalline module sheaf underlying `Ω_X/S`. -/
  module : CrystallineModuleSheaf S I γ h_compatible X x₀
  /-- The universal divided-power `S`-derivation into the module sheaf. -/
  derivation : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p module
  /-- The canonical comparison morphism for every crystalline thickening and
  divided-power relative differential owner. -/
  comparison : ∀ (T : CRIS S I γ h_compatible X x₀)
      (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent)
      (D : DividedPowerScheme.RelativeDifferentials
        (CrystallineObject.toDividedPowerScheme T h_quasiCoherent)
        S T.thickeningToBase),
      module.obj T ⟶ D.module
  /-- The comparison carries the universal derivation to the local divided-power derivation. -/
  comparison_derivation : ∀ (T : CRIS S I γ h_compatible X x₀)
    (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent)
    (D : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T h_quasiCoherent) S T.thickeningToBase),
    (derivation.component T).postcomp (comparison T h_quasiCoherent D).val =
      (d[T.thickeningToBase.toShHom]).postcomp D.quotient.val
  /-- Universal factorization through the crystalline derivation. -/
  universal : ∀ (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
      (D : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p F),
      ∃! q : CrystallineModuleMap S I γ h_compatible X x₀ module F,
        ∀ (T : CRIS S I γ h_compatible X x₀),
          (derivation.component T).postcomp (q.component T).val = D.component T

/-- Construct a universal crystalline differential owner from its sheaf,
derivation, comparison morphisms, and universal factorization property. -/
def CrystallineDifferentials.of
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
    (module : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (derivation : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p module)
    (comparison : ∀ (T : CRIS S I γ h_compatible X x₀)
      (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent)
      (D : DividedPowerScheme.RelativeDifferentials
        (CrystallineObject.toDividedPowerScheme T h_quasiCoherent)
        S T.thickeningToBase),
      module.obj T ⟶ D.module)
    (comparison_derivation : ∀ (T : CRIS S I γ h_compatible X x₀)
    (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent)
    (D : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T h_quasiCoherent) S T.thickeningToBase),
    (derivation.component T).postcomp (comparison T h_quasiCoherent D).val =
      (d[T.thickeningToBase.toShHom]).postcomp D.quotient.val)
    (universal : ∀ (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
      (D : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p F),
      ∃! q : CrystallineModuleMap S I γ h_compatible X x₀ module F,
        ∀ (T : CRIS S I γ h_compatible X x₀),
          (derivation.component T).postcomp (q.component T).val = D.component T) :
    CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p :=
  { module, derivation, comparison, comparison_derivation, universal }

/-- Universal crystalline differentials carry the local divided-power derivations
and represent divided-power derivations into every crystalline coefficient. -/
theorem CrystallineDifferentials.spec
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
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p) :
    (∀ (T : CRIS S I γ h_compatible X x₀)
      (h_quasiCoherent : T.ideal.toModule.IsQuasicoherent)
      (D : DividedPowerScheme.RelativeDifferentials
        (CrystallineObject.toDividedPowerScheme T h_quasiCoherent) S T.thickeningToBase),
      (Ω.derivation.component T).postcomp (Ω.comparison T h_quasiCoherent D).val =
        (d[T.thickeningToBase.toShHom]).postcomp D.quotient.val) ∧
    (∀ (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
      (D : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p F),
      ∃! q : CrystallineModuleMap S I γ h_compatible X x₀ Ω.module F,
        ∀ T : CRIS S I γ h_compatible X x₀,
          (Ω.derivation.component T).postcomp (q.component T).val = D.component T) :=
  ⟨Ω.comparison_derivation, Ω.universal⟩

/-- For a small crystalline object
`(U, T, δ)`, the universal crystalline differential sheaf restricts to the
canonical divided-power relative differential sheaf on `T`. -/
theorem CrystallineDifferentials.comparison_isIso
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
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase) :
    IsIso (Ω_XS.comparison T.obj.1 h_T_quasiCoherent D_T) := sorry

/-- The comparison identifying the
restriction of `d_{X/S}` with `d_{T/S,δ}` carries the universal sectionwise
derivation to the canonical divided-power derivation on every affine open. -/
theorem CrystallineDifferentials.comparison_spec
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
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase) :
    (Ω_XS.derivation.component T.obj.1).postcomp
        (Ω_XS.comparison T.obj.1 h_T_quasiCoherent D_T).val =
      (d[T.obj.1.thickeningToBase.toShHom]).postcomp D_T.quotient.val := sorry

/-- The universal crystalline sheaf of
differentials `Ω_{X/S}` is locally quasi-coherent. -/
theorem CrystallineDifferentials.isLocallyQuasiCoherent
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
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p) :
    CrystallineModuleSheaf.IsLocallyQuasiCoherent Ω_XS.module := sorry

/-- For a morphism of `Cris(X/S)` whose
thickening map `T ⟶ T'` is a closed immersion, the comparison
`c_φ : φ^*(Ω_{X/S})_{T'} ⟶ (Ω_{X/S})_T` is an epimorphism. -/
theorem CrystallineDifferentials.comparison_epi_of_closedImmersion
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
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T T' : smallCrystallineSite S I γ h_compatible X x₀)
    (φ : T ⟶ T')
    (h_closed : IsClosedImmersion φ.hom.thickening) :
    Epi (Ω_XS.module.comparison φ.hom) := sorry

/-- The universal crystalline differential coefficient has its intrinsic restriction and descent laws. -/
theorem CrystallineDifferentials.isCrisSheaf
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
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p) :
    CrystallineModuleSheaf.IsCrisSheaf p s h_p
      (CrystallineModuleSheaf.restrictCrystallineModule Ω_XS.module) := sorry


end
