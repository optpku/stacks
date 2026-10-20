/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap87.Lemma_87_19_13_Completion
public import stacks_project.Chap87.Lemma_87_19_13_Over
public import stacks_project.Chap87.Lemma_87_19_13_Functor
public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleSite

/-!
# Lemma 87.19.13

Formal spectrum identifies completed étale algebras, with continuous algebra
homomorphisms, contravariantly with representably étale affine formal algebraic
spaces over a weakly admissible formal spectrum. Every such domain is McQuillan.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/- Lemma 87.19.13. Formal spectrum of weak-ideal completions gives an equivalence
with the affine representably étale slice over the McQuillan formal spectrum. -/
@[stacks 0AN8]
#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.instIsEquivalence_spfEtaleCompletion hB :
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfEtaleCompletion hB).IsEquivalence)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.isMcQuillanAffine_of_affineEtaleOver hB :
  ∀ (X : AffineEtaleOver (spf B hB).obj),
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A) (hA : Spec (.of A) ⟶ S),
      Nonempty (X.obj.left ≅ (spf A hA).obj))
