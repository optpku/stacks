/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommDualResolution

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

/-- Actual restriction along the continuous geometric group map. -/
def restrict (M : NoncommCompactRepresentation.Cat R Γ) : NoncommCompactRepresentation.Cat R G :=
  ⟨(Action.res (NoncommCompactModule R) φ.toMonoidHom).obj M.obj, by sorry⟩

/-- The actual compact quotient by closed geometric relations. -/
abbrev quotient (M : NoncommCompactRepresentation.Cat R Γ) :=
  NoncommCompactTensor.coinvariants R G (restrict R G Γ φ M)

variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)

include hexact in
/-- Arithmetic translates preserve the closed geometric relation submodule. -/
theorem relations_stable (M : NoncommCompactRepresentation.Cat R Γ) (γ : Γ) :
    NoncommCompactTensor.relations R G (restrict R G Γ φ M) ≤
    (NoncommCompactTensor.relations R G (restrict R G Γ φ M)).comap
      (show _ →L[R] _ from M.obj.ρ γ).toLinearMap := by sorry

/-- The quotient-group action comes from translating representatives. -/
def action (M : NoncommCompactRepresentation.Cat R Γ) : Action (NoncommCompactModule R) Q where
  V := quotient R G Γ φ M
  ρ := { toFun := fun q ↦
          { toLinearMap := (NoncommCompactTensor.relations R G (restrict R G Γ φ M)).mapQ
              (NoncommCompactTensor.relations R G (restrict R G Γ φ M))
              (show _ →L[R] _ from M.obj.ρ (Function.surjInv hsurj q)).toLinearMap
              (relations_stable R G Γ Q φ ψ hexact M (Function.surjInv hsurj q))
            cont := by sorry }
         map_one' := by sorry
         map_mul' := by sorry }

/-- Quotient topology and joint continuity give the actual residual compact action. -/
theorem action_continuous (M : NoncommCompactRepresentation.Cat R Γ) :
    NoncommCompactRepresentation.continuousAction R Q (action R G Γ Q φ ψ hexact hsurj M) := by sorry

/-- Geometric coinvariants retaining the independent arithmetic quotient action. -/
def obj (M : NoncommCompactRepresentation.Cat R Γ) : NoncommCompactRepresentation.Cat R Q :=
  ⟨action R G Γ Q φ ψ hexact hsurj M, action_continuous R G Γ Q φ ψ hexact hsurj M⟩

/-- Equivariant continuous coefficient maps preserve closed relations. -/
theorem map_relations {M N : NoncommCompactRepresentation.Cat R Γ} (f : M ⟶ N) :
    NoncommCompactTensor.relations R G (restrict R G Γ φ M) ≤
    (NoncommCompactTensor.relations R G (restrict R G Γ φ N)).comap
      (show _ →L[R] _ from f.hom.hom).toLinearMap := by sorry

/-- Actual closed-quotient coefficient morphism with residual equivariance. -/
def map {M N : NoncommCompactRepresentation.Cat R Γ} (f : M ⟶ N) :
    obj R G Γ Q φ ψ hexact hsurj M ⟶ obj R G Γ Q φ ψ hexact hsurj N :=
  ObjectProperty.homMk
    { hom :=
        { toLinearMap := (NoncommCompactTensor.relations R G (restrict R G Γ φ M)).mapQ
            (NoncommCompactTensor.relations R G (restrict R G Γ φ N))
            (show _ →L[R] _ from f.hom.hom).toLinearMap (map_relations R G Γ φ f)
          cont := by sorry }
      comm := fun _ ↦ by sorry }

/-- Derivation is performed in all compact arithmetic representations. -/
def functor : NoncommCompactRepresentation.Cat R Γ ⥤ NoncommCompactRepresentation.Cat R Q where
  obj := obj R G Γ Q φ ψ hexact hsurj
  map := map R G Γ Q φ ψ hexact hsurj
  map_id := by sorry
  map_comp := by sorry

instance functor_additive : (functor R G Γ Q φ ψ hexact hsurj).Additive := by sorry

end NoncommResidualCoinvariants
