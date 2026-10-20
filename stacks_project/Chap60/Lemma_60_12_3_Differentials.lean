/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Definition_60_12_1_Derivation
public import stacks_project.Chap60.Lemma_60_12_2
public import stacks_project.Chap60.«60_10_0_2_ModuleSheaf»
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory
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

/-- A morphism of crystalline module sheaves, with its comparison naturality. -/
structure CrystallineModuleMap.{u_1}
    (S : Scheme.{u_1}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u_1}) (x₀ : X ⟶ I.subscheme)
    (F G : CrystallineModuleSheaf S I γ h_compatible X x₀) where
  /-- The module morphism on each crystalline object. -/
  component : ∀ T : CRIS S I γ h_compatible X x₀, F.obj T ⟶ G.obj T
  /-- The components commute with the comparison maps of the crystalline site. -/
  natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback f.thickening).map (component B) ≫ G.comparison f =
        F.comparison f ≫ component A

/-- Construct a natural morphism of crystalline module sheaves. -/
def CrystallineModuleMap.of
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (F G : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (component : ∀ T : CRIS S I γ h_compatible X x₀, F.obj T ⟶ G.obj T)
    (natural : ∀ {A B : CRIS S I γ h_compatible X x₀}
      (f : CrystallineObject.Hom A B),
      (Scheme.Modules.pullback f.thickening).map (component B) ≫ G.comparison f =
        F.comparison f ≫ component A) :
    CrystallineModuleMap S I γ h_compatible X x₀ F G :=
  { component, natural }

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
    (universal : ∀ (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
      (D : CrystallineModuleSheaf.SDerivation p S I γ h_compatible s X x₀ h_p F),
      ∃! q : CrystallineModuleMap S I γ h_compatible X x₀ module F,
        ∀ (T : CRIS S I γ h_compatible X x₀),
          (derivation.component T).postcomp (q.component T).val = D.component T) :
    CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p :=
  { module, derivation, comparison, universal }

end
