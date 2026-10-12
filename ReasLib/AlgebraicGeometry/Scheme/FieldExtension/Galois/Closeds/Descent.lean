/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Closeds

/-!
# Descent of Galois-invariant closed subsets

This module gives descent of closed subsets along a Galois field extension. A closed subset of a
base change fixed by every induced Galois automorphism is the inverse image of a closed subset of
the original scheme. Both the bundled fixed-point hypothesis and its explicit preimage formulation
are provided, together with range and membership characterizations.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Galois.Closeds.Descent

/-- A direct-Galois-invariant closed subset of a field-extension base change is pulled back from a
closed subset of the source. -/
theorem exists_preimage_eq
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f))
    (hTbar : Tbar ∈ FieldExtension.Galois.Closeds.invariant k K f) :
    ∃ T : TopologicalSpace.Closeds X,
      FieldExtension.Galois.Closeds.preimage k K f T = Tbar := sorry

/-- A closed subset of a field-extension base change that is stable under preimage by every induced
Galois automorphism is pulled back from a closed subset of the original scheme. -/
theorem exists_preimage_eq_of_preimage
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f))
    (hTbar :
      ∀ σ : Gal(K/k),
        Tbar.preimage
            ((FieldExtension.Galois.aut k K f σ).hom.continuous) = Tbar) :
    ∃ T : TopologicalSpace.Closeds X,
      FieldExtension.Galois.Closeds.preimage k K f T = Tbar := sorry

/-- The Galois-fixed closed subsets are exactly the pullbacks of closed subsets from the source. -/
theorem invariant_eq_range
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    FieldExtension.Galois.Closeds.invariant k K f =
      Set.range (fun T : TopologicalSpace.Closeds X ↦
        FieldExtension.Galois.Closeds.preimage k K f T) := sorry

/-- Membership in the Galois-fixed closed subsets is equivalent to being the pullback of a source
closed subset. -/
theorem mem_invariant_iff_exists_preimage
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (Tbar : TopologicalSpace.Closeds (FieldExtension.baseChange k K f)) :
    Tbar ∈ FieldExtension.Galois.Closeds.invariant k K f ↔
      ∃ T : TopologicalSpace.Closeds X,
        FieldExtension.Galois.Closeds.preimage k K f T = Tbar := sorry

end FieldExtension.Galois.Closeds.Descent

end AlgebraicGeometry
