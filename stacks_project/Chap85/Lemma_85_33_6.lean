/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfSpectralSequence

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Functor
open scoped Simplicial

universe u

/- Lemma 85.33.6: An fppf hypercovering of an algebraic space gives a canonical
spectral sequence from the étale cohomology of its stages to that of its
augmentation target. -/
@[stacks 0DHA] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.exists_etaleSpectralSequence :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      {U : SimplicialObject (AlgebraicSpace S)} →
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) →
      (ha : AlgebraicGeometry.AlgebraicSpace.Simplicial.IsFppfHypercovering a) →
      (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) →
      ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
        (pageOneIso : ∀ p q : ℕ,
          (E.page 1 le_rfl).X (p, q) ≅
            (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusCohomology
              (U.obj (op ⦋p⦌)) (q : ℤ)).obj
                ((AlgebraicGeometry.AlgebraicSpace.Simplicial.pullbackStage a p).obj F)),
        CohomologicalSpectralSequenceNat.ConvergesTo E
          (fun n : ℕ ↦
            (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusCohomology X (n : ℤ)).obj F))
