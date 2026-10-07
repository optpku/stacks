module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.HigherResidualComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactRightComposition

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientGeometry
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

/-- Restriction of all discrete representations is additive. -/
instance geometricRestriction_additive : (Ambient.restriction Λ X ηbar).Additive := sorry

/-- Group restriction is exact; it retains underlying modules and maps. -/
instance geometricRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (Ambient.restriction Λ X ηbar) := sorry

/-- Group restriction preserves finite colimits. -/
instance geometricRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (Ambient.restriction Λ X ηbar) := sorry

/-- For the closed geometric subgroup of the profinite arithmetic group,
restriction of an arithmetic injective is acyclic for continuous geometric invariants.
This does not assert preservation of injective objects by restriction. -/
theorem geometricRestriction_injective_acyclic
    (I : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))))
    (hI : Injective I) (n : ℕ) :
    IsZero ((AmbientDiscreteCohomology.cohomology Λ (Aut (standardFiniteEtaleFiber ηbar)) (n + 1)).obj
      ((Ambient.restriction Λ X ηbar).obj I)) := sorry

/-- Forgetting only the residual action gives the actual geometric invariant submodule functor. -/
def residualUnderlyingUnderivedIso :
    residualInvariantsFunctor Λ X ηbar ⋙ Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) ≅
      Ambient.restriction Λ X ηbar ⋙ AmbientDiscreteCohomology.invariants Λ
        (Aut (standardFiniteEtaleFiber ηbar)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The canonical underlying comparison uses homology-preserving action forgetfulness,
the actual underived identity, and the specified exact-precomposition resolution map. -/
def relativeUnderlyingIso (n : ℕ) :
    higherResidualInvariants Λ X ηbar n ⋙ Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) ≅
      Ambient.cohomology Λ X ηbar n :=
  (Functor.RightDerived.postcompIso (residualInvariantsFunctor Λ X ηbar)
      (Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)) n).symm ≪≫
    NatIso.rightDerived (residualUnderlyingUnderivedIso Λ X ηbar) n ≪≫
    ActualExactRightComposition.isoOfAcyclic (Ambient.restriction Λ X ηbar)
      (AmbientDiscreteCohomology.invariants Λ (Aut (standardFiniteEtaleFiber ηbar)))
      (geometricRestriction_injective_acyclic Λ X ηbar) n

/-- The familiar geometric continuous-cohomology model receives the actual relative
quotient action through a purely GROUP-THEORETIC resolution comparison.
No geometric cohomology comparison appears in this action's definition. -/
def continuousCohomologyGaloisAction
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) (n : ℕ) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := (Ambient.cohomology Λ X ηbar n).obj M
  ρ := (((relativeUnderlyingIso Λ X ηbar n).app M).conj.toMonoidHom).comp
    ((higherResidualInvariants Λ X ηbar n).obj M).ρ

end AlgebraicGeometry.SchemeOverField.AmbientGeometry
