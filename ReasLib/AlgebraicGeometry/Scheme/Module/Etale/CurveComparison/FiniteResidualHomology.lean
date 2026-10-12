/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteCompactInput

/-!
# Residual homology with the original finite left coefficients

Use the existing chosen compact resolution at the coefficient ring `Λᵐᵒᵖ`.
Its module chain has left `Λᵐᵒᵖᵐᵒᵖ` coefficients, which are restricted back to
`Λ` by the canonical ring equivalence. Neither the resolution nor the residual
action is replaced by a new chosen object or an ordinary restricted action.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace FiniteResidualHomology

variable (Λ G Γ Q : Type u) [Ring Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)
variable (M : DiscreteModuleCat Λ Γ) [Module.Finite Λ M.obj.V]

/-- The actual canonical residual chain, returned to the original left coefficient ring. -/
def chain : ChainComplex (ModuleCat.{u} Λ) ℕ :=
  ((ModuleCat.restrictScalars (RingEquiv.opOp Λ).toRingHom).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj
      (NoncommResidualHomology.moduleChain Λᵐᵒᵖ G Γ Q φ ψ hexact hsurj
        (FiniteCompactInput.residualInput M))

/-- Restriction of scalars preserves the specified residual Frobenius chain map. -/
def frobenius (q : Q) : chain Λ G Γ Q φ ψ hexact hsurj M ⟶
    chain Λ G Γ Q φ ψ hexact hsurj M :=
  ((ModuleCat.restrictScalars (RingEquiv.opOp Λ).toRingHom).mapHomologicalComplex
    (ComplexShape.down ℕ)).map
      (NoncommResidualHomology.chainFrobenius Λᵐᵒᵖ G Γ Q φ ψ hexact hsurj
        (FiniteCompactInput.residualInput M) q)

/-- The input coefficient action and the geometric comma quotient remain visible on every term. -/
theorem frobenius_projection (γ : Γ) (i : ℕ)
    (m : ((NoncommDualResolution.chosen Λᵐᵒᵖ Γ
      (FiniteCompactInput.residualInput M)).complex.X i).obj.V.toModule) :
    ((frobenius Λ G Γ Q φ ψ hexact hsurj M (ψ γ)).f i).hom
        (NoncommResidualCoinvariants.projection Λᵐᵒᵖᵐᵒᵖ G Γ φ
          ((NoncommDualResolution.chosen Λᵐᵒᵖ Γ
            (FiniteCompactInput.residualInput M)).complex.X i) m) =
      NoncommResidualCoinvariants.projection Λᵐᵒᵖᵐᵒᵖ G Γ φ
        ((NoncommDualResolution.chosen Λᵐᵒᵖ Γ
          (FiniteCompactInput.residualInput M)).complex.X i)
        ((show _ →L[Λᵐᵒᵖᵐᵒᵖ] _ from
          ((NoncommDualResolution.chosen Λᵐᵒᵖ Γ
            (FiniteCompactInput.residualInput M)).complex.X i).obj.ρ γ) m) :=
  NoncommResidualHomology.chainFrobenius_projection Λᵐᵒᵖ G Γ Q φ ψ hexact hsurj
    (FiniteCompactInput.residualInput M) γ i m

/-- The resulting residual endomorphism is linear over the original left coefficient ring. -/
theorem frobenius_smul (q : Q) (i : ℕ) (a : Λ)
    (m : (chain Λ G Γ Q φ ψ hexact hsurj M).X i) :
    ((frobenius Λ G Γ Q φ ψ hexact hsurj M q).f i).hom (a • m) =
      a • ((frobenius Λ G Γ Q φ ψ hexact hsurj M q).f i).hom m :=
  ((frobenius Λ G Γ Q φ ψ hexact hsurj M q).f i).hom.map_smul a m

end FiniteResidualHomology
