/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Lemma_72_12_7_Closeds

/-!
# Galois descent of closed subsets of algebraic spaces

A Galois-invariant closed subset of `|X_K|` is the inverse image of a closed
subset of `|X|` along `|X_K| → |X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace FieldExtension.Galois.Closeds

/-- Lemma 72.12.7: Let `k` be a field. Let `K / k` be a (possibly infinite) Galois
extension. Let `X` be an algebraic space over `k`. Let `Tbar ⊂ |X_K|` be a closed
subset such that `σ(Tbar) = Tbar` for every `σ : Gal(K/k)`. Then there exists a
closed subset `T ⊂ |X|` whose inverse image along `|X_K| → |X|` is `Tbar`. -/
@[stacks 0A16]
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
