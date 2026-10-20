/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualSectionsComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedCochainTransport
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommResidualGaloisTransport
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))

/-- Restrict the residual action along the specified inverse continuous
fiber-group/Galois equivalence, leaving coefficient vectors unchanged. -/
def toGalois : DiscreteModuleCat R (ActualResidualCompletedTarget.residualGroup X η) ⥤
    DiscreteModuleCat R Gal(AlgebraicClosure k/k) where
  obj M := ⟨(Action.res (ModuleCat.{u + 1} R)
    (ActualResidualCompletedTarget.residualEquiv X η).symm.toMonoidHom).obj M.obj, by sorry⟩
  map f := ObjectProperty.homMk ((Action.res (ModuleCat.{u + 1} R)
    (ActualResidualCompletedTarget.residualEquiv X η).symm.toMonoidHom).map f.hom)
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance toGalois_additive : (toGalois R X η).Additive := by sorry

/-- Identity on vectors recovers the original Galois action after both naming transports. -/
def namingIso : NoncommResidualSectionsComparison.toResidual R X η ⋙ toGalois R X η ≅
    𝟭 (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (Action.mkIso (Iso.refl M.obj.V) (fun _ ↦ by sorry))) (by sorry)

/-- Exact coefficient-preserving transport to actual pointwise completed modules. -/
def completed := toGalois R X η ⋙ NoncommPointwiseCompletedAction.functor R Gal(AlgebraicClosure k/k)

instance completed_additive : (completed R X η).Additive :=
  inferInstanceAs ((toGalois R X η ⋙
    NoncommPointwiseCompletedAction.functor R Gal(AlgebraicClosure k/k)).Additive)
instance completed_preservesFiniteLimits : PreservesFiniteLimits (completed R X η) := by sorry
instance completed_preservesFiniteColimits : PreservesFiniteColimits (completed R X η) := by sorry

end NoncommResidualGaloisTransport
