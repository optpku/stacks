/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldModuleDescent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldExactTransport
variable (k : Type u) [Field k] (R : Type (u + 1)) [Ring R]
variable [HasWeakSheafify (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} R)]

instance forward_isEquivalence : (FieldModuleDescent.forward k R).IsEquivalence :=
  (FieldModuleDescent.equivalence k R).isEquivalence_functor
instance inverse_isEquivalence : (FieldModuleDescent.inverse k R).IsEquivalence :=
  (FieldModuleDescent.equivalence k R).isEquivalence_inverse

instance forward_preservesFiniteLimits : PreservesFiniteLimits (FieldModuleDescent.forward k R) := by infer_instance
instance forward_preservesFiniteColimits : PreservesFiniteColimits (FieldModuleDescent.forward k R) := by infer_instance
instance inverse_preservesFiniteLimits : PreservesFiniteLimits (FieldModuleDescent.inverse k R) := by infer_instance
instance inverse_preservesFiniteColimits : PreservesFiniteColimits (FieldModuleDescent.inverse k R) := by infer_instance

instance forward_additive : (FieldModuleDescent.forward k R).Additive := by sorry
instance inverse_additive : (FieldModuleDescent.inverse k R).Additive := by sorry

end FieldExactTransport
