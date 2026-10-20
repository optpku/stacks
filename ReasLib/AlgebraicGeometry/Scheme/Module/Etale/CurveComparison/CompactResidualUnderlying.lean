module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricResidualHomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactLeftComposition

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.CompactResidual
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

/-- Actual compact restriction to the closed geometric subgroup. -/
def restriction := CompactResidualHomology.restrictFunctor Λ
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) (geometricToArithmetic X ηbar).hom

/-- Compact group restriction is additive and exact. -/
instance restriction_additive : (restriction Λ X ηbar).Additive := sorry

/-- Compact group restriction preserves finite limits. -/
instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction Λ X ηbar) := sorry

/-- Compact group restriction preserves finite colimits, without requiring projective preservation. -/
instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction Λ X ηbar) := sorry

/-- Forget only the residual quotient action, retaining the actual compact module. -/
def underlyingResidual : CompactRepresentation.Cat Λ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar)))) ⥤ CompactModule Λ :=
  (CompactRepresentation.continuousAction Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar))))).ι ⋙
    Action.forget (CompactModule Λ)
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar))))

/-- Forgetting the compact residual action is additive. -/
instance underlyingResidual_additive : (underlyingResidual Λ X ηbar).Additive := sorry

/-- Kernels and closed-image quotients are unchanged when the compact action is forgotten. -/
instance underlyingResidual_preservesHomology : (underlyingResidual Λ X ηbar).PreservesHomology := sorry

/-- The two underived routes are the SAME closed geometric quotient on objects and maps. -/
def underlyingUnderivedIso :
    restriction Λ X ηbar ⋙ CompactRepresentation.coinvariantsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) ≅
      geometricCoinvariantsFunctor Λ X ηbar ⋙ underlyingResidual Λ X ηbar :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- Restriction of a compact arithmetic projective is geometric-coinvariants-acyclic,
dually to closed-subgroup acyclicity of restricted arithmetic injectives. -/
theorem restriction_projective_acyclic
    (P : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    (hP : Projective P) (n : ℕ) :
    IsZero ((CompactRepresentation.continuousHomology Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) (n + 1)).obj
      ((restriction Λ X ηbar).obj P)) := sorry

/-- The underlying comparison to Kuhn's compact geometric homology is built
from ACTUAL projective chain lifts and the exact action-forgetting map. -/
def underlyingHomologyIso (n : ℕ) :
    restriction Λ X ηbar ⋙ CompactRepresentation.continuousHomology Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n ≅
      homology Λ X ηbar n ⋙ underlyingResidual Λ X ηbar :=
  ActualExactLeftComposition.isoOfAcyclic (restriction Λ X ηbar)
      (CompactRepresentation.coinvariantsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)))
      (restriction_projective_acyclic Λ X ηbar) n ≪≫
    ActualLeftDerived.mapIso (underlyingUnderivedIso Λ X ηbar) n ≪≫
    ActualLeftDerived.postcompIso (geometricCoinvariantsFunctor Λ X ηbar) (underlyingResidual Λ X ηbar) n

/-- Kuhn's actual geometric compact-homology object receives its residual action
through a purely GROUP-THEORETIC projective-resolution comparison. -/
def geometricHomologyGaloisAction
    (M : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))) (n : ℕ) :
    Action (CompactModule Λ) Gal(AlgebraicClosure k/k) where
  V := (CompactRepresentation.continuousHomology Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).obj
    ((restriction Λ X ηbar).obj M)
  ρ := (((underlyingHomologyIso Λ X ηbar n).app M).symm.conj.toMonoidHom).comp
    ((galoisHomology Λ X ηbar n).obj M).ρ

end AlgebraicGeometry.SchemeOverField.CompactResidual
