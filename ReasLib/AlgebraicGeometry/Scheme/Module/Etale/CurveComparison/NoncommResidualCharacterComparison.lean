/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualInvariants

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace NoncommResidualCharacterComparison
variable (R G Γ Q : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)
variable (M : DiscreteModuleCat R Γ)

abbrev inv := (NoncommResidualInvariants.functor R G Γ Q φ ψ hexact hsurj).obj M
abbrev dual := NoncommRepresentationDuality.dual R Γ M
abbrev coinv := (NoncommResidualCoinvariants.functor Rᵐᵒᵖ G Γ Q φ ψ hexact hsurj).obj (dual R Γ M)

/-- Restrict an actual additive character to the invariant vectors. -/
def restriction : (dual R Γ M).obj.V ⟶
    (NoncommRepresentationDuality.dual R Q (inv R G Γ Q φ ψ hexact hsurj M)).obj.V :=
  NoncommCompactCharacters.map R (inv R G Γ Q φ ψ hexact hsurj M).obj.V
    (ModuleCat.ofHom (NoncommResidualInvariants.invariants R G Γ φ M).subtype)

/-- Restriction kills the CLOSED geometric character relations: continuity
extends vanishing on generators to their closure. -/
theorem relations_le_kernel :
    NoncommCompactTensor.relations Rᵐᵒᵖ G
      (NoncommResidualCoinvariants.restrict Rᵐᵒᵖ G Γ φ (dual R Γ M)) ≤
    LinearMap.ker (show _ →L[Rᵐᵒᵖ] _ from restriction R G Γ Q φ ψ hexact hsurj M).toLinearMap := by sorry

/-- The quotient map has exactly the restricted-character function. -/
def descend : (coinv R G Γ Q φ ψ hexact hsurj M).obj.V.toModule →ₗ[Rᵐᵒᵖ]
    (NoncommRepresentationDuality.dual R Q (inv R G Γ Q φ ψ hexact hsurj M)).obj.V.toModule :=
  (NoncommCompactTensor.relations Rᵐᵒᵖ G
    (NoncommResidualCoinvariants.restrict Rᵐᵒᵖ G Γ φ (dual R Γ M))).liftQ
      (show _ →L[Rᵐᵒᵖ] _ from restriction R G Γ Q φ ψ hexact hsurj M).toLinearMap
      (relations_le_kernel R G Γ Q φ ψ hexact hsurj M)

theorem descend_continuous : Continuous (descend R G Γ Q φ ψ hexact hsurj M) := by sorry

/-- Pontryagin duality identifies this quotient with characters of invariants.
This is NOT an infinite algebraic bidual claim. -/
theorem descend_bijective : Function.Bijective (descend R G Γ Q φ ψ hexact hsurj M) := by sorry

def linearEquiv := LinearEquiv.ofBijective (descend R G Γ Q φ ψ hexact hsurj M)
  (descend_bijective R G Γ Q φ ψ hexact hsurj M)

theorem inverse_continuous : Continuous (linearEquiv R G Γ Q φ ψ hexact hsurj M).symm := by sorry

/-- The actual compact quotient/restriction comparison and its continuous inverse. -/
def moduleIso : (coinv R G Γ Q φ ψ hexact hsurj M).obj.V ≅
    (NoncommRepresentationDuality.dual R Q (inv R G Γ Q φ ψ hexact hsurj M)).obj.V where
  hom := { toLinearMap := descend R G Γ Q φ ψ hexact hsurj M
           cont := descend_continuous R G Γ Q φ ψ hexact hsurj M }
  inv := { toLinearMap := (linearEquiv R G Γ Q φ ψ hexact hsurj M).symm.toLinearMap
           cont := inverse_continuous R G Γ Q φ ψ hexact hsurj M }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Residual action is retained through the original arithmetic translations. -/
def iso : coinv R G Γ Q φ ψ hexact hsurj M ≅
    NoncommRepresentationDuality.dual R Q (inv R G Γ Q φ ψ hexact hsurj M) :=
  ObjectProperty.isoMk _ (Action.mkIso (moduleIso R G Γ Q φ ψ hexact hsurj M) (fun _ ↦ by sorry))

variable {M}

/-- Naturality is restriction of the same character precompositions on both sides. -/
theorem naturality {N : DiscreteModuleCat R Γ} (f : M ⟶ N) :
    (NoncommResidualCoinvariants.functor Rᵐᵒᵖ G Γ Q φ ψ hexact hsurj).map
      (NoncommRepresentationDuality.dualMap R Γ f) ≫ (iso R G Γ Q φ ψ hexact hsurj M).hom =
    (iso R G Γ Q φ ψ hexact hsurj N).hom ≫ NoncommRepresentationDuality.dualMap R Q
      ((NoncommResidualInvariants.functor R G Γ Q φ ψ hexact hsurj).map f) := by sorry

end NoncommResidualCharacterComparison
