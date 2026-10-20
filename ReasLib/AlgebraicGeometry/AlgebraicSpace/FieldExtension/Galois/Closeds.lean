/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Closed subsets of field-extension base changes of algebraic spaces

Closed subsets pull back along the field-extension projection and the canonical
Galois-induced automorphisms. Invariance under a Galois automorphism is equivalent
to invariance under its pullback on closed subsets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace FieldExtension.Galois.Closeds

/-- Pull a closed subset of `|X|` back along `|X_K| → |X|`. -/
noncomputable abbrev preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (T : Closeds (Points X)) :
    Closeds (Points (FieldExtension.baseChange k K X)) :=
  T.preimage (Points.continuous_map (FieldExtension.baseChangeSnd k K X))

/-- Pull a closed subset of `|X_K|` back along the automorphism induced by
`σ : Gal(K/k)`. -/
noncomputable abbrev galoisPreimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (σ : Gal(K/k))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X))) :
    Closeds (Points (FieldExtension.baseChange k K X)) :=
  Tbar.preimage (Points.continuous_map (FieldExtension.Galois.map k K X σ))

/-- The underlying set of a closed subset pulled back from `|X|` is the ordinary
preimage along `|X_K| → |X|`. -/
theorem coe_preimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (T : Closeds (Points X)) :
    (preimage k K T : Set (Points (FieldExtension.baseChange k K X))) =
      Points.map (FieldExtension.baseChangeSnd k K X) ⁻¹' (T : Set (Points X)) :=
  sorry

/-- The underlying set of a Galois closed preimage is the ordinary preimage along
the induced map on points. -/
theorem coe_galoisPreimage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (σ : Gal(K/k))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X))) :
    (galoisPreimage k K σ Tbar : Set (Points (FieldExtension.baseChange k K X))) =
      Points.map (FieldExtension.Galois.map k K X σ) ⁻¹'
        (Tbar : Set (Points (FieldExtension.baseChange k K X))) :=
  sorry

/-- Galois-invariance of a closed subset of `|X_K|` may be checked as a preimage
equality or as an image equality. -/
theorem galoisPreimage_eq_iff_image
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (of k))} (σ : Gal(K/k))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X))) :
    galoisPreimage k K σ Tbar = Tbar ↔
      Points.map (FieldExtension.Galois.map k K X σ) '' (Tbar : Set _) =
        (Tbar : Set _) :=
  sorry

end FieldExtension.Galois.Closeds
end AlgebraicGeometry.AlgebraicSpace
