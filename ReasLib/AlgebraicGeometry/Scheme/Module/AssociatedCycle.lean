/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization

/-!
# Associated cycles of coherent modules

This file defines the cycle associated to a coherent module in a fixed dimension and records
its coefficient formula and dimension support.
-/

@[expose] public section

open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The stalk-length coefficient function of a coherent module, restricted to its
dimension-`k` minimal support points, has locally finite support. -/
theorem associatedCycleLocallyFiniteSupport (F : X.Modules) [F.IsCoherent]
    (d : X → ℤ) (k : ℤ) :
    LocallyFiniteSupport (fun x : X ↦
      @ite ℤ (x ∈ X.minimalSpecializationPoints (moduleSupport F) ∧ d x = k)
        (Classical.propDecidable _)
        ((Module.length (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)).toNat : ℤ)
        0) := sorry

/-- The degree-`k` cycle associated to a coherent module, with coefficients given by
the lengths of its stalks at the minimal points of its support. -/
noncomputable def associatedCycle (F : X.Modules) [F.IsCoherent]
    (d : X → ℤ) (k : ℤ) : AlgebraicCycle X ℤ :=
  { toFun := fun x ↦
      @ite ℤ (x ∈ X.minimalSpecializationPoints (moduleSupport F) ∧ d x = k)
        (Classical.propDecidable _)
        ((Module.length (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)).toNat : ℤ)
        0
    supportWithinDomain' := Set.subset_univ _
    supportLocallyFiniteWithinDomain' := fun x _ ↦
      associatedCycleLocallyFiniteSupport F d k x }

/-- The coefficient of `F.associatedCycle d k` is the stalk length at a minimal support point
of dimension `k`, and is zero elsewhere. -/
theorem associatedCycle_apply (F : X.Modules) [F.IsCoherent]
    (d : X → ℤ) (k : ℤ) (x : X) :
    F.associatedCycle d k x =
      @ite ℤ (x ∈ X.minimalSpecializationPoints (moduleSupport F) ∧ d x = k)
        (Classical.propDecidable _)
        ((Module.length (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)).toNat : ℤ)
        0 := sorry

/-- The cycle associated to `F` in degree `k` is supported in dimension `k`. -/
theorem associatedCycle_mem_dimensionSubgroup (F : X.Modules) [F.IsCoherent]
    (d : X → ℤ) (k : ℤ) :
    F.associatedCycle d k ∈ AlgebraicCycle.dimensionSubgroup d k := sorry

end AlgebraicGeometry.Scheme.Modules
