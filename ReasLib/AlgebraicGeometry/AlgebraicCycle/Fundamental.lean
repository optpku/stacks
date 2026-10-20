/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum

/-!
# Fundamental algebraic cycles

This file defines the fundamental cycle of a locally Noetherian scheme and its decomposition
into generic-point components.
-/

@[expose] public section

open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The multiplicity of a generic point is the finite length of its local ring over itself. -/
noncomputable def genericMultiplicity (X : Scheme.{u}) [IsLocallyNoetherian X]
    (η : genericPoints X) : ℕ :=
  (Module.length (X.presheaf.stalk η.1) (X.presheaf.stalk η.1)).toNat

/-- The generic-point multiplicity recovers the length of the corresponding local ring. -/
theorem genericMultiplicity_eq_length (X : Scheme.{u}) [IsLocallyNoetherian X]
    (η : genericPoints X) :
    (genericMultiplicity X η : ℕ∞) =
      Module.length (X.presheaf.stalk η.1) (X.presheaf.stalk η.1) := sorry

/-- The coefficient function defining the degree-`k` fundamental cycle has locally finite
support. -/
theorem fundamentalLocallyFiniteSupport (d : X → ℤ) (k : ℤ) :
    LocallyFiniteSupport (fun x ↦
      @dite ℤ (x ∈ genericPoints X ∧ d x = k) (Classical.propDecidable _)
        (fun hx ↦ (genericMultiplicity X ⟨x, hx.1⟩ : ℤ)) (fun _ ↦ 0)) := sorry

/-- The degree-`k` fundamental cycle of a locally Noetherian scheme with dimension function `d`. -/
noncomputable def fundamental (d : X → ℤ) (k : ℤ) : AlgebraicCycle X ℤ :=
  { toFun := fun x ↦
      @dite ℤ (x ∈ genericPoints X ∧ d x = k) (Classical.propDecidable _)
        (fun hx ↦ (genericMultiplicity X ⟨x, hx.1⟩ : ℤ)) (fun _ ↦ 0)
    supportWithinDomain' := Set.subset_univ _
    supportLocallyFiniteWithinDomain' := fun x _ ↦ fundamentalLocallyFiniteSupport d k x }

/-- At a generic point of degree `k`, the fundamental-cycle coefficient is its generic
multiplicity. -/
theorem fundamental_apply_generic (d : X → ℤ) (k : ℤ) (η : genericPoints X)
    (hη : d η.1 = k) :
    fundamental d k η.1 = (genericMultiplicity X η : ℤ) := sorry

/-- The fundamental cycle vanishes at points which are not generic points. -/
theorem fundamental_eq_zero_of_not_generic (d : X → ℤ) (k : ℤ) (x : X)
    (hx : x ∉ genericPoints X) :
    fundamental d k x = 0 := sorry

/-- The singleton component terms of a fundamental cycle form a locally finite family. -/
theorem fundamentalComponentsLocallyFinite (d : X → ℤ) (k : ℤ) :
    LocallyFinite fun η : genericPoints X ↦
      (if d η.1 = k then
        @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
          η.1 (genericMultiplicity X η : ℤ)
      else 0).support := sorry

/-- A fundamental cycle is the locally finite sum of its generic-point components. -/
theorem fundamental_eq_sum_components (d : X → ℤ) (k : ℤ) :
    fundamental d k = locallyFiniteSum
      (fun η : genericPoints X ↦
        if d η.1 = k then
          @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
            η.1 (genericMultiplicity X η : ℤ)
        else 0)
      (fundamentalComponentsLocallyFinite d k) := sorry

end AlgebraicGeometry.AlgebraicCycle
