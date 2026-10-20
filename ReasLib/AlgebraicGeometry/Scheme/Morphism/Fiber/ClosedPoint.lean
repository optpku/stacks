/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed points of scheme-theoretic fibres

For a morphism locally of finite type, a point is closed in its fibre exactly when the induced
extension of residue fields is finite.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Let `f : X ⟶ S` be locally of finite type. A point `x` is closed in the fibre over `f x` if
and only if `κ(x) / κ(f(x))` is finite. -/
@[stacks 01TF]
theorem asFiber_mem_closedPoints_iff_moduleFinite_residueField
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    f.asFiber x ∈ closedPoints (f.fiber (f x)) ↔
      Module.Finite (S.residueField (f x)) (X.residueField x) := by
  constructor
  · intro hx
    -- Local instance justification (proof-local temporary data): register the closed immersion
    -- derived from `hx` only for the adjacent finite-type argument.
    letI : IsClosedImmersion (f.asFiberHom x) :=
      IsClosedImmersion.of_isPreimmersion _ (by
        rw [f.range_asFiberHom x]
        exact hx)
    -- Local instance justification (proof-local temporary data): register the finite-type
    -- property derived from the closed immersion only for the adjacent composition step.
    haveI : LocallyOfFiniteType (f.asFiberHom x) := inferInstance
    -- Local instance justification (proof-local temporary data): register the pullback-derived
    -- finite-type property only for the adjacent comparison step.
    haveI : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    -- Local instance justification (proof-local temporary data): register the finite-type
    -- property derived from the comparison equality only for the adjacent ring-map step.
    haveI : LocallyOfFiniteType (Spec.map (f.residueFieldMap x)) := by
      rw [← f.asFiberHom_fiberToSpecResidueField x]
      infer_instance
    have hft : (f.residueFieldMap x).hom.FiniteType :=
      HasRingHomProperty.Spec_iff.mp
        (show LocallyOfFiniteType (Spec.map (f.residueFieldMap x)) from inferInstance)
    change (f.residueFieldMap x).hom.Finite
    exact RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hft
  · intro hfin
    have hft : (f.residueFieldMap x).hom.FiniteType := by
      apply RingHom.FiniteType.of_finite
      exact hfin
    -- Local instance justification (proof-local temporary data): register the finite-type
    -- property derived from `hft` only for the adjacent composition step.
    haveI : LocallyOfFiniteType (Spec.map (f.residueFieldMap x)) :=
      HasRingHomProperty.Spec_iff.mpr hft
    -- Local instance justification (proof-local temporary data): register the finite-type
    -- property derived from the comparison equality only for the adjacent cancellation step.
    haveI : LocallyOfFiniteType
        (f.asFiberHom x ≫ f.fiberToSpecResidueField (f x)) := by
      rw [f.asFiberHom_fiberToSpecResidueField x]
      infer_instance
    -- Local instance justification (proof-local temporary data): register the finite-type
    -- property derived from the composite only for the adjacent closed-point image step.
    haveI : LocallyOfFiniteType (f.asFiberHom x) :=
      locallyOfFiniteType_of_comp (f.asFiberHom x)
        (f.fiberToSpecResidueField (f x))
    have h := (f.asFiberHom x).closePoints_subset_preimage_closedPoints
      (IsLocalRing.isClosed_singleton_closedPoint (X.residueField x))
    simpa using h

/-- If the residue-field extension at a point of a scheme morphism is algebraic, then the
corresponding point of the scheme-theoretic fibre is closed. -/
theorem asFiber_mem_closedPoints_of_isAlgebraic_residueField
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (halg : Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x)) :
    f.asFiber x ∈ closedPoints (f.fiber (f x)) := sorry

/-- A point with algebraic residue-field extension is closed when its image under the scheme
morphism is closed. -/
theorem mem_closedPoints_of_isAlgebraic_residueField_of_image_mem_closedPoints
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (halg : Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x))
    (hs : f x ∈ closedPoints S) :
    x ∈ closedPoints X := sorry

end AlgebraicGeometry
