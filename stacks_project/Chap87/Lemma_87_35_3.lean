/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.StructureSheaf.Cohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.35.3: the structure sheaf of a countably indexed affine formal
algebraic space has vanishing étale cohomology in every positive degree. -/
@[stacks 0DEL] #check (AlgebraicGeometry.FormalAlgebraicSpace.isZero_cohomology_structureSheaf :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [AffineFormalAlgebraicSpace.IsCountablyIndexedAffine X] [Reduction X]
    (𝒪 : Sheaf (AlgebraicSpace.smallEtaleTopology (reduction X)) RingCat.{u})
    [IsStructureSheaf 𝒪] (n : ℕ) (hn : 0 < n)
    [HasSheafify (AlgebraicSpace.smallEtaleTopology (reduction X)) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (AlgebraicSpace.smallEtaleTopology (reduction X)) AddCommGrpCat.{u})],
    IsZero
      ((Sheaf.functorH (AlgebraicSpace.smallEtaleTopology (reduction X)) n).obj
        ((sheafCompose (AlgebraicSpace.smallEtaleTopology (reduction X))
            (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj 𝒪)))
