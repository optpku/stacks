/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.UniversalProperty
import StacksCheckRecall

/-!
# Lemma 71.17.5

A chosen blowing up of a closed subspace of an algebraic space is a final
object of the full subcategory of spaces over the ambient space on which the
inverse image of the center is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Blowup

noncomputable section

universe u

/- Lemma 71.17.5 (Universal property blowing up): for a scheme `S`, an algebraic
space `X` over `S`, and a closed subspace `Z ⊂ X`, a chosen blowing up
`π : along Z` is a final object of the full subcategory of `Over X` consisting
of morphisms whose inverse image of `Z` is an effective Cartier divisor. -/
@[stacks 085U] #check
  (AlgebraicGeometry.AlgebraicSpace.effectiveCartierPullbackOverCategory.existsUnique_hom :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : ClosedSubspace X) →
      (π : along Z) → (Y : effectiveCartierPullbackOverCategory Z) →
        ExistsUnique fun f : Y ⟶ effectiveCartierPullbackOverCategory.blowupObject Z π ↦
          f.hom.left ≫ Blowup.alongHom Z π = Y.obj.hom)

