/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic

/-!
# Closed subsets of a Galois field-extension base change

This leaf keeps closed subsets bundled as `TopologicalSpace.Closeds`.  It exposes the two
contravariant pullback operations used by descent arguments: pullback along the source projection
and pullback along a Galois-induced automorphism.  The latter is packaged as both the direct and
opposite Galois actions, so downstream statements can choose the indexing convention they use for
other field-extension invariants.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Closeds

/-- Pull a closed subset of `X` back to the field-extension base change of `X`. -/
noncomputable abbrev preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : TopologicalSpace.Closeds X) :
    TopologicalSpace.Closeds (FieldExtension.baseChange k K f) :=
  T.preimage (FieldExtension.toSource k K f).continuous

/-- Pull a closed subset of a field-extension base change back along the automorphism induced by
`σ : Gal(K / k)`. -/
noncomputable abbrev galoisPreimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    TopologicalSpace.Closeds (FieldExtension.baseChange k K f) :=
  Tbar.preimage ((FieldExtension.Galois.aut k K f σ).hom.continuous)

/-- Pullback along the identity Galois automorphism leaves a closed subset unchanged. -/
theorem galoisPreimage_one
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    FieldExtension.Galois.Closeds.galoisPreimage k K f (1 : Gal(K/k)) Tbar = Tbar := sorry

/-- Galois multiplication is sent to iterated closed-subset preimage in the same order. -/
theorem galoisPreimage_mul
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ τ : Gal(K/k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    FieldExtension.Galois.Closeds.galoisPreimage k K f (σ * τ) Tbar =
      FieldExtension.Galois.Closeds.galoisPreimage k K f σ
        (FieldExtension.Galois.Closeds.galoisPreimage k K f τ Tbar) := sorry

/-- Pulling a source closed subset back to the field-extension base change is invariant under
every Galois closed-subset preimage. -/
theorem galoisPreimage_preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k))
    (T : TopologicalSpace.Closeds X) :
    FieldExtension.Galois.Closeds.galoisPreimage k K f σ
        (FieldExtension.Galois.Closeds.preimage k K f T) =
      FieldExtension.Galois.Closeds.preimage k K f T := sorry

/-- The direct Galois action on closed subsets.  The Galois-induced scheme maps are
anti-multiplicative, and taking preimages reverses their composition once more. -/
noncomputable instance instMulAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MulAction Gal(K/k) (TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) where
  smul σ Tbar := FieldExtension.Galois.Closeds.galoisPreimage k K f σ Tbar
  one_smul := sorry
  mul_smul := sorry

/-- The opposite-Galois action on closed subsets, indexed with the inverse needed for the
contravariant closed-subset action. -/
noncomputable instance instOppositeMulAction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    MulAction (Gal(K/k))ᵐᵒᵖ
      (TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) where
  smul σ Tbar := FieldExtension.Galois.Closeds.galoisPreimage k K f σ.unop.symm Tbar
  one_smul := sorry
  mul_smul := sorry

/-- Computation rule for the direct Galois action on closed subsets. -/
theorem smul_def
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : Gal(K/k)) (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    σ • Tbar = FieldExtension.Galois.Closeds.galoisPreimage k K f σ Tbar := sorry

/-- Computation rule for the opposite-Galois action on closed subsets. -/
theorem op_smul_def
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : (Gal(K/k))ᵐᵒᵖ)
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    σ • Tbar = FieldExtension.Galois.Closeds.galoisPreimage k K f σ.unop.symm Tbar := sorry

/-- The set of closed subsets fixed by the direct Galois action. -/
noncomputable abbrev invariant
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Set (TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :=
  MulAction.fixedPoints (Gal(K/k))
    (TopologicalSpace.Closeds (FieldExtension.baseChange k K f))

/-- The set of closed subsets fixed by the opposite-Galois action. -/
noncomputable abbrev opInvariant
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Set (TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :=
  MulAction.fixedPoints (Gal(K/k))ᵐᵒᵖ
    (TopologicalSpace.Closeds (FieldExtension.baseChange k K f))

/-- Membership in the direct fixed-point set is the usual all-elements invariance predicate. -/
theorem mem_invariant_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    Tbar ∈ FieldExtension.Galois.Closeds.invariant k K f ↔
      ∀ σ : Gal(K/k), σ • Tbar = Tbar := sorry

/-- Membership in the direct fixed-point set can be checked using the explicit Galois preimage
operation. -/
theorem mem_invariant_iff_preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    Tbar ∈ FieldExtension.Galois.Closeds.invariant k K f ↔
      ∀ σ : Gal(K/k),
        FieldExtension.Galois.Closeds.galoisPreimage k K f σ Tbar = Tbar := sorry

/-- The fixed-point predicate in the literal bundled-`Closeds` preimage notation. -/
theorem mem_invariant_iff_preimage_eq
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    Tbar ∈ FieldExtension.Galois.Closeds.invariant k K f ↔
      ∀ σ : Gal(K/k),
        Tbar.preimage
            ((FieldExtension.Galois.aut k K f σ).hom.continuous) = Tbar := sorry

/-- The fixed-point predicate is equivalent to stability under the images of all induced scheme
automorphisms. -/
theorem mem_invariant_iff_image
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    Tbar ∈ FieldExtension.Galois.Closeds.invariant k K f ↔
      ∀ σ : Gal(K/k),
        (Scheme.homeoOfIso (FieldExtension.Galois.aut k K f σ)) ''
            (Tbar : Set (FieldExtension.baseChange k K f)) =
          (Tbar : Set (FieldExtension.baseChange k K f)) := sorry

/-- Membership in the opposite fixed-point set is the all-elements invariance predicate for the
opposite action. -/
theorem mem_opInvariant_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    Tbar ∈ FieldExtension.Galois.Closeds.opInvariant k K f ↔
      ∀ σ : (Gal(K/k))ᵐᵒᵖ, σ • Tbar = Tbar := sorry

/-- The underlying set of a closed subset pulled back from `X` is the ordinary topological
preimage along the source projection. -/
theorem coe_preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : TopologicalSpace.Closeds X) :
    (FieldExtension.Galois.Closeds.preimage k K f T : Set
      (FieldExtension.baseChange k K f)) =
      (FieldExtension.toSource k K f).base ⁻¹' (T : Set X) := sorry

/-- The underlying set of a Galois closed preimage is the ordinary topological preimage along the
induced scheme automorphism. -/
theorem coe_galoisPreimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    (FieldExtension.Galois.Closeds.galoisPreimage k K f σ Tbar : Set
      (FieldExtension.baseChange k K f)) =
      (FieldExtension.Galois.aut k K f σ).hom.base ⁻¹' (Tbar : Set _) := sorry

/-- The pullback of every closed subset from `X` is fixed by the Galois action. -/
theorem preimage_mem_invariant
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (T : TopologicalSpace.Closeds X) :
    FieldExtension.Galois.Closeds.preimage k K f T ∈
      FieldExtension.Galois.Closeds.invariant k K f := sorry

end FieldExtension.Galois.Closeds

end AlgebraicGeometry
