module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualCharacterComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommDerivedTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurveHomSign

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace NoncommResidualDualComplex
variable (R G Γ Q : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)
variable {M : DiscreteModuleCat R Γ} (I : InjectiveResolution M)

/-- Actual compact character reversal of the residual-invariants complex. -/
def characterChain : ChainComplex (NoncommCompactRepresentation.Cat Rᵐᵒᵖ Q) ℕ where
  X i := NoncommRepresentationDuality.dual R Q
    ((NoncommResidualInvariants.functor R G Γ Q φ ψ hexact hsurj).obj (I.cocomplex.X i))
  d i j := NoncommRepresentationDuality.dualMap R Q
    ((NoncommResidualInvariants.functor R G Γ Q φ ψ hexact hsurj).map (I.cocomplex.d j i))
  shape := by sorry
  d_comp_d' := by sorry

/-- Character restriction on EACH actual injective term intertwines the
reversed differentials and retains the residual Q-action. -/
def chainIso :
    ((NoncommResidualCoinvariants.functor Rᵐᵒᵖ G Γ Q φ ψ hexact hsurj).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (NoncommDualResolution.chain R Γ I) ≅
    characterChain R G Γ Q φ ψ hexact hsurj I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ NoncommResidualCharacterComparison.iso R G Γ Q φ ψ hexact hsurj (I.cocomplex.X i))
    (by intro i j hij; exact (NoncommResidualCharacterComparison.naturality R G Γ Q φ ψ hexact hsurj (I.cocomplex.d j i)).symm)

variable (K : NoncommCompactRepresentation.Cat Rᵐᵒᵖ Γ)

/-- Use exactly the continuous-character injective resolution underlying the
chosen compact projective resolution in the existing completed-tensor target. -/
abbrev resolution := injectiveResolution (NoncommRepresentationDuality.inverseDiscrete R Γ K)

def completedCharacterCochain :=
  (((NoncommCompletedAction.functor Rᵐᵒᵖ Q).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (characterChain R G Γ Q φ ψ hexact hsurj (resolution R Γ K))).extend
      CompactRepresentation.curveDegreeEmbedding

/-- The same group-side chain comparison after the actual completed action
and the approved degree 2-i embedding. -/
def cochainIso : NoncommDerivedTensor.coinvariantCochain R G Γ Q φ ψ hexact hsurj K ≅
    completedCharacterCochain R G Γ Q φ ψ hexact hsurj K :=
  (CompactRepresentation.curveDegreeEmbedding.extendFunctor _).mapIso
    (((NoncommCompletedAction.functor Rᵐᵒᵖ Q).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (chainIso R G Γ Q φ ψ hexact hsurj (resolution R Γ K)))

/-- The Hom convention introduces the already kernel-verified alternating
phase, normalized to identity in top trace degree 2. -/
def signedCharacterCochain := ActualCurveHomSign.signed
  (completedCharacterCochain R G Γ Q φ ψ hexact hsurj K)

/-- Explicit signed compact character-to-completed-tensor assembly. Its arrows
are phase scalars, character restriction, and finite balanced-tensor projections. -/
def tensorIso : signedCharacterCochain R G Γ Q φ ψ hexact hsurj K ≅
    NoncommDerivedTensor.tensorCochain R G Γ Q φ ψ hexact hsurj K :=
  (ActualCurveHomSign.iso (completedCharacterCochain R G Γ Q φ ψ hexact hsurj K)).symm ≪≫
  (cochainIso R G Γ Q φ ψ hexact hsurj K).symm ≪≫
  NoncommDerivedTensor.cochainIso R G Γ Q φ ψ hexact hsurj K

end NoncommResidualDualComplex
