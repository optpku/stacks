/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.Closeds

/-!
# Galois descent of closed subsets of algebraic spaces

For a possibly infinite Galois extension, a closed subset of the base change of
an algebraic space descends if it is invariant under every Galois automorphism.
Both image and preimage formulations of invariance are provided.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace FieldExtension.Galois.Closeds

/-- A closed subset of `|X_K|` stable under every Galois closed preimage is the
inverse image of a closed subset of `|X|`. -/
theorem exists_preimage_eq_of_preimage
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : AlgebraicSpace (Spec (of k)))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X)))
    (h_preimage : ∀ σ : Gal(K/k), galoisPreimage k K σ Tbar = Tbar) :
    ∃ T : Closeds (Points X), preimage k K T = Tbar :=
  sorry

/-- For a possibly infinite Galois extension `K / k`, every closed subset of
`|X_K|` invariant under all Galois-induced automorphisms is the inverse image of
a closed subset of `|X|`. -/
theorem exists_preimage_eq_of_image
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (X : AlgebraicSpace (Spec (of k)))
    (Tbar : Closeds (Points (FieldExtension.baseChange k K X)))
    (h_image : ∀ σ : Gal(K/k),
      Points.map (FieldExtension.Galois.map k K X σ) '' (Tbar : Set _) =
        (Tbar : Set _)) :
    ∃ T : Closeds (Points X), preimage k K T = Tbar :=
  sorry

end FieldExtension.Galois.Closeds
end AlgebraicGeometry.AlgebraicSpace
