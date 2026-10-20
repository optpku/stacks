/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualCoinvariants

@[expose] public section
open CategoryTheory
noncomputable section
universe u

namespace NoncommResidualCoinvariants

variable (R G Γ Q : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)

/-- The actual closed-coinvariant projection, without any abstract quotient identification. -/
def projection (M : NoncommCompactRepresentation.Cat R Γ) :
    M.obj.V.toModule →ₗ[R] (quotient R G Γ φ M).toModule :=
  (NoncommCompactTensor.relations R G (restrict R G Γ φ M)).mkQ

omit [Finite R] [IsTopologicalGroup G] [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- Geometric translates have the same image in the closed quotient. -/
theorem projection_geometric (M : NoncommCompactRepresentation.Cat R Γ) (g : G)
    (m : M.obj.V.toModule) :
    projection R G Γ φ M ((show _ →L[R] _ from M.obj.ρ (φ g)) m) =
      projection R G Γ φ M m := by
  apply (Submodule.Quotient.eq _).mpr
  exact Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self (g, m)))

omit [Finite R] [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- Categorical composition gives the real multiplication order on coefficients. -/
theorem translate_mul (M : NoncommCompactRepresentation.Cat R Γ) (a b : Γ)
    (m : M.obj.V.toModule) :
    (show _ →L[R] _ from M.obj.ρ (a * b)) m =
      (show _ →L[R] _ from M.obj.ρ a) ((show _ →L[R] _ from M.obj.ρ b) m) := by
  rw [map_mul]
  rfl

omit [Finite R] [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- Translations are conjugation-twisted equivariant, with the actual coefficient map. -/
theorem translate_conjugate (M : NoncommCompactRepresentation.Cat R Γ) (a b : Γ)
    (m : M.obj.V.toModule) :
    (show _ →L[R] _ from M.obj.ρ a) ((show _ →L[R] _ from M.obj.ρ b) m) =
      (show _ →L[R] _ from M.obj.ρ (a * b * a⁻¹))
        ((show _ →L[R] _ from M.obj.ρ a) m) := by
  rw [← translate_mul, ← translate_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Quotient representatives compute by the actual lift used in the canonical owner. -/
theorem action_projection (M : NoncommCompactRepresentation.Cat R Γ) (q : Q)
    (m : M.obj.V.toModule) :
    (show _ →L[R] _ from (action R G Γ Q φ ψ hexact hsurj M).ρ q)
        (projection R G Γ φ M m) =
      projection R G Γ φ M
        ((show _ →L[R] _ from M.obj.ρ (Function.surjInv hsurj q)) m) := rfl

/-- The formula is independent of the selected lift: it is translation by any arithmetic lift. -/
theorem action_projection_lift (M : NoncommCompactRepresentation.Cat R Γ) (γ : Γ)
    (m : M.obj.V.toModule) :
    (show _ →L[R] _ from (action R G Γ Q φ ψ hexact hsurj M).ρ (ψ γ))
        (projection R G Γ φ M m) =
      projection R G Γ φ M ((show _ →L[R] _ from M.obj.ρ γ) m) := by
  rw [action_projection]
  let δ := Function.surjInv hsurj (ψ γ)
  have hδ : ψ δ = ψ γ := Function.surjInv_eq hsurj (ψ γ)
  have hker : δ * γ⁻¹ ∈ MonoidHom.ker ψ.toMonoidHom := by
    change ψ (δ * γ⁻¹) = 1
    rw [map_mul, map_inv, hδ, mul_inv_cancel]
  rw [← hexact] at hker
  obtain ⟨g, hg⟩ := hker
  have hmul : φ g * γ = δ := by
    change φ g = δ * γ⁻¹ at hg
    rw [hg, mul_assoc, inv_mul_cancel, mul_one]
  change projection R G Γ φ M ((show _ →L[R] _ from M.obj.ρ δ) m) = _
  rw [← hmul, translate_mul]
  exact projection_geometric R G Γ φ M g _

end NoncommResidualCoinvariants
