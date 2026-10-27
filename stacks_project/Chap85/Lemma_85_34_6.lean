/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.SpectralSequence

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

/- Lemma 85.34.6: An fppf hypercovering of an algebraic space gives a canonical
spectral sequence with first page H^q_étale(U_p, F_p), converging to
H^{p+q}_étale(X, F), for every quasi-coherent module F. -/
@[stacks 0DHH] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.exists_qcohEtaleSpectralSequence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
      (ha : IsFppfHypercovering a)
      (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory),
      ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
        (pageOneIso : ∀ p q : ℕ,
          (E.page 1 le_rfl).X (p, q) ≅ stageModuleCohomology a F.obj p q),
        CohomologicalSpectralSequenceNat.ConvergesTo E
          (spacesEtaleModuleCohomology X F.obj))
