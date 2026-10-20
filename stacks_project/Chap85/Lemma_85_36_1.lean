/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.PhComparison
import StacksCheckRecall

/-! # Lemma 85.36.1 -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped MorphismOfTopoiIn

/- Lemma 85.36.1. Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` an augmentation. There is a
commutative diagram of topoi
`Sh (sliceTotalTopology (phTopology S) U) ⟶ Sh (spacesEtaleTotalTopology U)` over
`Sh (bigPhSite X) ⟶ Sh (spacesEtaleTopology X)`, whose left vertical arrow is the
Section 85.21 slice augmentation and whose right vertical arrow is the
Section 85.32 étale augmentation. -/
@[stacks 0DHJ] #check (AlgebraicGeometry.AlgebraicSpace.Simplicial.phEtaleAugmentationInverseImageIso :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (U : SimplicialObject (AlgebraicSpace S))
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (phEtaleComparison U)⁻¹ ≅
      (spacesPhComparison X)⁻¹ ⋙ (phAugmentation U a)⁻¹)
