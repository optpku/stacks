/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Closeds.Descent

@[expose] public section

universe u

/- Lemma 33.7.10: Galois-invariant closed subsets descend from a field-extension base change. -/
@[stacks 038B] #check
  (AlgebraicGeometry.FieldExtension.Galois.Closeds.Descent.exists_preimage_eq_of_preimage :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
      {X : AlgebraicGeometry.Scheme.{u}},
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) →
      (Tbar : TopologicalSpace.Closeds
        (AlgebraicGeometry.FieldExtension.baseChange k K f)) →
      (∀ σ : Gal(K/k),
        Tbar.preimage
          ((AlgebraicGeometry.FieldExtension.Galois.aut k K f σ).hom.continuous) = Tbar) →
      ∃ T : TopologicalSpace.Closeds X,
        AlgebraicGeometry.FieldExtension.Galois.Closeds.preimage k K f T = Tbar)
