/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.Algebra.TensorProduct.EqLocus

/-!
# Equalizer rings after coefficient base change

This module constructs the induced endpoint maps, their equalizer ring, and the canonical map
from the new coefficient ring.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u

namespace RingHom.EqLocusBaseChange

variable {A B C' : Type u} [CommRing A] [CommRing B] [CommRing C']

/-- The source map restricts to the common equalizer action. -/
theorem source_commutes (target source : A →+* B) (r : target.eqLocus source) :
    source (algebraMap (target.eqLocus source) A r) =
      (source.comp (target.eqLocus source).subtype) r := rfl

/-- The target map restricts to the common equalizer action. -/
theorem target_commutes (target source : A →+* B) (r : target.eqLocus source) :
    target (algebraMap (target.eqLocus source) A r) =
      (source.comp (target.eqLocus source).subtype) r := r.property

/-- The object-ring span: the equalizer inclusion and the chosen coefficient map.
Its tensor product is the base-changed object ring. -/
def objectSpan (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    Algebra.TensorProduct.RingHom.Span
      (X := target.eqLocus source) (Y := A) (Z := C') where
  left := (target.eqLocus source).subtype
  right := γ

/-- The arrow-ring span uses the source-induced action of the equalizer.
The target induces the same action by `target_commutes`. -/
def arrowSpan (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    Algebra.TensorProduct.RingHom.Span
      (X := target.eqLocus source) (Y := B) (Z := C') where
  left := source.comp (target.eqLocus source).subtype
  right := γ

/-- Base change of the source map along a map from the equalizer ring. -/
def sourceComap (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    (objectSpan target source γ).tensor →+* (arrowSpan target source γ).tensor :=
  -- Local instances: the explicit spans select the actions for this tensor map only.
  letI := (objectSpan target source γ).leftAlgebra
  letI := (arrowSpan target source γ).leftAlgebra
  letI := (objectSpan target source γ).rightAlgebra
  let sourceHom : A →ₐ[target.eqLocus source] B :=
    { source with commutes' := source_commutes target source }
  (Algebra.TensorProduct.map sourceHom (AlgHom.id (target.eqLocus source) C')).toRingHom

/-- The base-changed source map acts componentwise on pure tensors. -/
theorem sourceComap_tmul (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (a : A) (c : C') :
    sourceComap target source γ ((objectSpan target source γ).tmul a c) =
      (arrowSpan target source γ).tmul (source a) c := rfl

/-- Base change of the target map along a map from the equalizer ring. -/
def targetComap (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    (objectSpan target source γ).tensor →+* (arrowSpan target source γ).tensor :=
  -- Local instances: the explicit spans select the actions for this tensor map only.
  letI := (objectSpan target source γ).leftAlgebra
  letI := (arrowSpan target source γ).leftAlgebra
  letI := (objectSpan target source γ).rightAlgebra
  let targetHom : A →ₐ[target.eqLocus source] B :=
    { target with commutes' := target_commutes target source }
  (Algebra.TensorProduct.map targetHom (AlgHom.id (target.eqLocus source) C')).toRingHom

/-- The base-changed target map acts componentwise on pure tensors. -/
theorem targetComap_tmul (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (a : A) (c : C') :
    targetComap target source γ ((objectSpan target source γ).tmul a c) =
      (arrowSpan target source γ).tmul (target a) c := rfl

/-- The source tensor map restricts to the original source on the left factor. -/
theorem sourceComap_comp_includeLeft (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    (sourceComap target source γ).comp (objectSpan target source γ).includeLeft =
      (arrowSpan target source γ).includeLeft.comp source := by
  ext a
  rfl

/-- The target tensor map restricts to the original target on the left factor. -/
theorem targetComap_comp_includeLeft (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    (targetComap target source γ).comp (objectSpan target source γ).includeLeft =
      (arrowSpan target source γ).includeLeft.comp target := by
  ext a
  rfl

/-- The source tensor map preserves the coefficient inclusion. -/
theorem sourceComap_comp_includeRight (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    (sourceComap target source γ).comp (objectSpan target source γ).includeRight =
      (arrowSpan target source γ).includeRight := by
  ext c
  change (arrowSpan target source γ).tmul (source 1) c =
    (arrowSpan target source γ).tmul 1 c
  rw [map_one]

/-- The target tensor map preserves the coefficient inclusion. -/
theorem targetComap_comp_includeRight (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    (targetComap target source γ).comp (objectSpan target source γ).includeRight =
      (arrowSpan target source γ).includeRight := by
  ext c
  change (arrowSpan target source γ).tmul (target 1) c =
    (arrowSpan target source γ).tmul 1 c
  rw [map_one]

/-- The invariant ring after coefficient base change is the equalizer of the induced endpoint
maps. -/
def invariantRing (target source : A →+* B)
    (γ : target.eqLocus source →+* C') : Subring (objectSpan target source γ).tensor :=
  (targetComap target source γ).eqLocus (sourceComap target source γ)

/-- Membership in the base-changed invariant ring is equality of the two induced endpoint maps. -/
theorem mem_invariantRing (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (x : (objectSpan target source γ).tensor) :
    x ∈ invariantRing target source γ ↔
      targetComap target source γ x = sourceComap target source γ x := Iff.rfl

/-- The right tensor inclusion takes values in the base-changed invariant ring. -/
theorem includeRight_mem_invariantRing (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (c : C') :
    (objectSpan target source γ).includeRight c ∈ invariantRing target source γ := by
  change ((targetComap target source γ).comp
    (objectSpan target source γ).includeRight) c =
    ((sourceComap target source γ).comp (objectSpan target source γ).includeRight) c
  rw [targetComap_comp_includeRight, sourceComap_comp_includeRight]

/-- The canonical map from the new coefficient ring to the base-changed invariant ring. -/
def toInvariant (target source : A →+* B)
    (γ : target.eqLocus source →+* C') : C' →+* invariantRing target source γ :=
  RingHom.codRestrict (objectSpan target source γ).includeRight
    (invariantRing target source γ) (includeRight_mem_invariantRing target source γ)

/-- The canonical map sends a coefficient to the right pure tensor `1 ⊗ₜ c`. -/
theorem toInvariant_apply (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (c : C') :
    (toInvariant target source γ c : (objectSpan target source γ).tensor) =
      (objectSpan target source γ).tmul 1 c := rfl

/-- Composing the canonical map with the invariant-subring inclusion gives the right tensor
inclusion. -/
theorem val_comp_toInvariant (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    (invariantRing target source γ).subtype.comp (toInvariant target source γ) =
      (objectSpan target source γ).includeRight := by
  ext c
  rfl

end RingHom.EqLocusBaseChange
