/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      (source.comp (target.eqLocus source).subtype) r := sorry

/-- The target map restricts to the common equalizer action. -/
theorem target_commutes (target source : A →+* B) (r : target.eqLocus source) :
    target (algebraMap (target.eqLocus source) A r) =
      (source.comp (target.eqLocus source).subtype) r := sorry

/-- Base change of the source map along a map from the equalizer ring. -/
def sourceComap (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    A ⊗[target.eqLocus source] C' →+* B ⊗[target.eqLocus source] C' :=
  -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
  letI : Algebra (target.eqLocus source) B :=
    (source.comp (target.eqLocus source).subtype).toAlgebra
  -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
  letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
  let sourceHom : A →ₐ[target.eqLocus source] B :=
    { source with commutes' := source_commutes target source }
  (Algebra.TensorProduct.map sourceHom (AlgHom.id (target.eqLocus source) C')).toRingHom

/-- The base-changed source map acts componentwise on pure tensors. -/
theorem sourceComap_tmul (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (a : A) (c : C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    sourceComap target source γ (a ⊗ₜ[target.eqLocus source] c) =
      source a ⊗ₜ[target.eqLocus source] c := sorry

/-- Base change of the target map along a map from the equalizer ring. -/
def targetComap (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    A ⊗[target.eqLocus source] C' →+* B ⊗[target.eqLocus source] C' :=
  -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
  letI : Algebra (target.eqLocus source) B :=
    (source.comp (target.eqLocus source).subtype).toAlgebra
  -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
  letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
  let targetHom : A →ₐ[target.eqLocus source] B :=
    { target with commutes' := target_commutes target source }
  (Algebra.TensorProduct.map targetHom (AlgHom.id (target.eqLocus source) C')).toRingHom

/-- The base-changed target map acts componentwise on pure tensors. -/
theorem targetComap_tmul (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (a : A) (c : C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    targetComap target source γ (a ⊗ₜ[target.eqLocus source] c) =
      target a ⊗ₜ[target.eqLocus source] c := sorry

/-- The invariant ring after coefficient base change is the equalizer of the induced endpoint
maps. -/
def invariantRing (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    Subring (A ⊗[target.eqLocus source] C') :=
  -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
  letI : Algebra (target.eqLocus source) B :=
    (source.comp (target.eqLocus source).subtype).toAlgebra
  -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
  letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
  (targetComap target source γ).eqLocus (sourceComap target source γ)

/-- Membership in the base-changed invariant ring is equality of the two induced endpoint maps. -/
theorem mem_invariantRing (target source : A →+* B)
    (γ : target.eqLocus source →+* C')
    (x :
      -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
      letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
      A ⊗[target.eqLocus source] C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    x ∈ invariantRing target source γ ↔
      targetComap target source γ x = sourceComap target source γ x := sorry

/-- The right tensor inclusion takes values in the base-changed invariant ring. -/
theorem includeRight_mem_invariantRing (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (c : C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    (Algebra.TensorProduct.includeRight :
      C' →ₐ[target.eqLocus source] A ⊗[target.eqLocus source] C') c ∈
        invariantRing target source γ := sorry

/-- The canonical map from the new coefficient ring to the base-changed invariant ring. -/
def toInvariant (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    C' →+* invariantRing target source γ :=
  -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
  letI : Algebra (target.eqLocus source) B :=
    (source.comp (target.eqLocus source).subtype).toAlgebra
  -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
  letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
  RingHom.codRestrict Algebra.TensorProduct.includeRight.toRingHom
    (invariantRing target source γ) (includeRight_mem_invariantRing target source γ)

/-- The canonical map sends a coefficient to the right pure tensor `1 ⊗ₜ c`. -/
theorem toInvariant_apply (target source : A →+* B)
    (γ : target.eqLocus source →+* C') (c : C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    (toInvariant target source γ c : A ⊗[target.eqLocus source] C') =
      1 ⊗ₜ[target.eqLocus source] c := sorry

/-- Composing the canonical map with the invariant-subring inclusion gives the right tensor
inclusion. -/
theorem val_comp_toInvariant (target source : A →+* B)
    (γ : target.eqLocus source →+* C') :
    -- Local instance justification (defeq pin): use the source-induced equalizer action on `B` without registering a parameterized global instance.
    letI : Algebra (target.eqLocus source) B :=
      (source.comp (target.eqLocus source).subtype).toAlgebra
    -- Local instance justification (defeq pin): use the coefficient action selected by the explicit map `γ` only in this tensor expression.
    letI : Algebra (target.eqLocus source) C' := γ.toAlgebra
    (invariantRing target source γ).subtype.comp (toInvariant target source γ) =
      Algebra.TensorProduct.includeRight.toRingHom := sorry

end RingHom.EqLocusBaseChange
