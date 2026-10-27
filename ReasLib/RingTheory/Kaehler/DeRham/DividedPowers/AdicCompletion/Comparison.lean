/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.AdicCompletion
public import ReasLib.RingTheory.AdicCompletion.Quotient.Ideal
public import ReasLib.RingTheory.AdicCompletion.PrincipalMaps
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits KaehlerDifferential.DeRham

universe u

namespace DividedPowerDifferential

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) {J : Ideal B} (δ : DividedPowers J) (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Int.LocalizationAtPrime p) A]
variable (h_nilpotent : IsNilpotent (p : B ⧸ J))

/-- Completion of the original divided-power differential module, with its original-ring action. -/
abbrev originalCompletion : ModuleCat.{u} B :=
  ModuleCat.of B (AdicCompletion (Ideal.span {(p : B)}) (dividedPowerDifferential f δ))

/-- Completion of the completed ring's divided-power differentials, restricted to the original ring. -/
abbrev iteratedCompletion : ModuleCat.{u} B :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  (ModuleCat.restrictScalars (algebraMap B R)).obj
    (ModuleCat.of R (AdicCompletion (Ideal.span {(p : R)}) (completedDifferential f δ p h_nilpotent)))

/-- The canonical comparison of completed differential modules, assembled through their quotient limits. -/
def completedFormsComparisonIso :
    originalCompletion f δ p ≅ iteratedCompletion f δ p h_nilpotent :=
  let R := AdicCompletion (Ideal.span {(p : B)}) B
  let restriction := ModuleCat.restrictScalars (algebraMap B R)
  let system := AdicCompletion.positiveQuotientSystem (Ideal.span {(p : R)})
    (completedDifferential f δ p h_nilpotent)
  (AdicCompletion.positiveQuotientLimitIso (Ideal.span {(p : B)})
      (dividedPowerDifferential f δ)).symm ≪≫
    asIso (originalLimitComparison f δ p h_nilpotent) ≪≫
    (asIso (completionLimitComparison f δ p h_nilpotent)).symm ≪≫
    (preservesLimitIso restriction system).symm ≪≫
    restriction.mapIso (AdicCompletion.positiveQuotientLimitIso (Ideal.span {(p : R)})
      (completedDifferential f δ p h_nilpotent))

/-- The underlying original-ring-linear map of the canonical completed differential comparison. -/
def completedFormsComparison :
    originalCompletion f δ p →ₗ[B] iteratedCompletion f δ p h_nilpotent :=
  (completedFormsComparisonIso f δ p h_nilpotent).hom.hom

/-- The completed differential comparison respects every scalar in the completed ring. -/
theorem completedFormsComparison_smul
    (r : AdicCompletion (Ideal.span {(p : B)}) B) (ω : originalCompletion f δ p) :
    completedFormsComparison f δ p h_nilpotent (r • ω) =
      r • completedFormsComparison f δ p h_nilpotent ω := sorry

/-- The canonical comparison is linear over the completed coefficient ring. -/
def completedFormsEquiv :
    AdicCompletion (Ideal.span {(p : B)}) (dividedPowerDifferential f δ) ≃ₗ[
      AdicCompletion (Ideal.span {(p : B)}) B]
      AdicCompletion (Ideal.span {(p : AdicCompletion (Ideal.span {(p : B)}) B)})
        (completedDifferential f δ p h_nilpotent) :=
  { (completedFormsComparisonIso f δ p h_nilpotent).toLinearEquiv.toAddEquiv with
    map_smul' := completedFormsComparison_smul f δ p h_nilpotent }

/-- The comparison takes an original universal differential to the corresponding completed differential. -/
theorem completedFormsComparison_differential (b : B) :
    completedFormsComparison f δ p h_nilpotent
        (AdicCompletion.of (Ideal.span {(p : B)}) _ (dividedPowerDifferentialDerivation f δ b)) =
      AdicCompletion.of (Ideal.span {(p : AdicCompletion (Ideal.span {(p : B)}) B)}) _
        (dividedPowerDifferentialDerivation
          ((algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)).comp f)
          (completedRing δ p h_nilpotent).dividedPowers
          (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B) b)) := sorry

/-- The differential comparison intertwines continuous differentiation on all completed coefficients. -/
theorem completedFormsComparison_derivation (r : AdicCompletion (Ideal.span {(p : B)}) B) :
    completedFormsComparison f δ p h_nilpotent
        (AdicCompletion.completeAddMap B B p (dividedPowerDifferentialDerivation f δ).toAddMonoidHom r) =
      AdicCompletion.of (Ideal.span {(p : AdicCompletion (Ideal.span {(p : B)}) B)}) _
        (dividedPowerDifferentialDerivation
          ((algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)).comp f)
          (completedRing δ p h_nilpotent).dividedPowers r) := sorry

/-- Every valid quotient bound gives the canonical distinguished ideal of the completed divided-power ring. -/
theorem completionIdeal_eq (N : ℕ) (hN : Ideal.span {(p : B)} ^ N ≤ J) :
    RingHom.ker (AdicCompletion.toQuotient (Ideal.span {(p : B)}) J N hN) =
      (completedRing δ p h_nilpotent).ideal := sorry

/-- A compatible completion extension agrees with the canonical divided powers after ideal transport. -/
theorem completionDividedPowers_eq (N : ℕ) (hN : Ideal.span {(p : B)} ^ N ≤ J)
    (γhat : DividedPowers (RingHom.ker (AdicCompletion.toQuotient (Ideal.span {(p : B)}) J N hN)))
    (hγhat : δ.IsDPMorphism γhat (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B))) :
    (completionIdeal_eq δ p h_nilpotent N hN) ▸ γhat =
      (completedRing δ p h_nilpotent).dividedPowers := sorry

/-- The differential completion comparison for any compatible extension on a quotient kernel. -/
def completedFormsEquivOfExtension (N : ℕ) (hN : Ideal.span {(p : B)} ^ N ≤ J)
    (γhat : DividedPowers (RingHom.ker (AdicCompletion.toQuotient (Ideal.span {(p : B)}) J N hN)))
    (hγhat : δ.IsDPMorphism γhat (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B))) :
    AdicCompletion (Ideal.span {(p : B)}) (dividedPowerDifferential f δ) ≃ₗ[
      AdicCompletion (Ideal.span {(p : B)}) B]
      AdicCompletion (Ideal.span {(p : AdicCompletion (Ideal.span {(p : B)}) B)})
        (dividedPowerDifferential ((algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)).comp f) γhat) :=
  let hI := completionIdeal_eq δ p h_nilpotent N hN
  let hγ := completionDividedPowers_eq δ p h_nilpotent N hN γhat hγhat
  let family (K : Ideal (AdicCompletion (Ideal.span {(p : B)}) B)) (ε : DividedPowers K) :=
    AdicCompletion (Ideal.span {(p : B)}) (dividedPowerDifferential f δ) ≃ₗ[
      AdicCompletion (Ideal.span {(p : B)}) B]
      AdicCompletion (Ideal.span {(p : AdicCompletion (Ideal.span {(p : B)}) B)})
        (dividedPowerDifferential ((algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)).comp f) ε)
  let transport (K L : Ideal (AdicCompletion (Ideal.span {(p : B)}) B)) (h : K = L)
      (ε : DividedPowers K) (ε' : DividedPowers L) (he : h ▸ ε = ε') :
      family L ε' → family K ε :=
    match h, he with
    | rfl, rfl => id
  transport _ _ hI γhat (completedRing δ p h_nilpotent).dividedPowers hγ
    (completedFormsEquiv f δ p h_nilpotent)

/-- The differential completion comparison for a compatible extension on the image of the original ideal. -/
def completedFormsEquivOfImageExtension (N : ℕ) (hN : Ideal.span {(p : B)} ^ N ≤ J)
    (γhat : DividedPowers (Ideal.map (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)) J))
    (hγhat : δ.IsDPMorphism γhat (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B))) :
    AdicCompletion (Ideal.span {(p : B)}) (dividedPowerDifferential f δ) ≃ₗ[
      AdicCompletion (Ideal.span {(p : B)}) B]
      AdicCompletion (Ideal.span {(p : AdicCompletion (Ideal.span {(p : B)}) B)})
        (dividedPowerDifferential ((algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)).comp f) γhat) :=
  let hI := AdicCompletion.map_eq_ker_toQuotient (Ideal.span {(p : B)}) J
    (Submodule.fg_span_singleton (p : B)) N hN
  Eq.rec (motive := fun K _ ↦ ∀ (ε : DividedPowers K),
      δ.IsDPMorphism ε (algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)) →
      AdicCompletion (Ideal.span {(p : B)}) (dividedPowerDifferential f δ) ≃ₗ[
        AdicCompletion (Ideal.span {(p : B)}) B]
        AdicCompletion (Ideal.span {(p : AdicCompletion (Ideal.span {(p : B)}) B)})
          (dividedPowerDifferential ((algebraMap B (AdicCompletion (Ideal.span {(p : B)}) B)).comp f) ε))
    (fun ε hε ↦ completedFormsEquivOfExtension f δ p h_nilpotent N hN ε hε)
    hI.symm γhat hγhat

end DividedPowerDifferential
