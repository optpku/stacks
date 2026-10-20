/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.PhComparison
import StacksCheckRecall

/-!
# Lemma 85.33.1

For a scheme `S`, an algebraic space `X` over `S`, a simplicial algebraic space
`U` over `S`, and an augmentation `a : U ⟶ X`, the stagewise fppf-to-étale
comparisons assemble to a commutative square of morphisms of topoi
`Sh((Spaces/U)_{fppf,total}) ⟶ Sh(U_étale)` over
`Sh((Spaces/X)_{fppf}) ⟶ Sh(X_étale)`. The left vertical arrow is the
Section 85.21 slice-augmentation; the right vertical arrow is the Section 85.32
étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped MorphismOfTopoiIn

/- Lemma 85.33.1
Let S be a scheme. Let X be an algebraic space over S. Let U be a simplicial
algebraic space over S. Let a : U ⟶ X be an augmentation. The morphisms of
topoi h, a_fppf, a and h₋₁ form a commutative square of inverse images
(a)⁻¹ ⋙ h⁻¹ ≅ (h₋₁)⁻¹ ⋙ (a_fppf)⁻¹. -/
@[stacks 0DH5] #check (AlgebraicGeometry.AlgebraicSpace.Simplicial.fppfEtaleCommSq :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)) {X : AlgebraicSpace S}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X),
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (fppfEtaleComparison U)⁻¹ ≅
      (spacesFppfComparison X)⁻¹ ⋙ (fppfAugmentation U a)⁻¹)
