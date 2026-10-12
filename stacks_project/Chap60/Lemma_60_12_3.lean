/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Logic.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import stacks_project.Chap60.«60_10_0_2_ModuleSheaf»
public import stacks_project.Chap60.«60_9_1_1»
public import stacks_project.Chap60.Definition_60_6_1
public import stacks_project.Chap60.Lemma_60_12_3_Differentials
public import stacks_project.Chap60.Remark_60_6_7_Forms

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

universe u

/-- Lemma 60.12.3 (1): in Situation 60.7.5, for a crystalline object
`(U, T, δ)`, the universal crystalline differential sheaf restricts to the
canonical divided-power relative differential sheaf on `T`. -/
@[stacks 07IZ, instance]
instance crystallineDifferentials_restrict
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

/-- Lemma 60.12.3 (2): in Situation 60.7.5, the isomorphism identifying the
restriction of `d_{X/S}` with `d_{T/S,δ}` carries the universal sectionwise
derivation to the canonical divided-power derivation on every affine open. -/
@[stacks 07IZ]
theorem crystallineDifferential_restrict
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
