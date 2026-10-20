/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure

@[expose] public section

open CategoryTheory

universe u

/- Lemma 40.11.3: for an identity-on-objects morphism of groupoid schemes, the target
composition maps the fibre product of the reduced closure of the arrow-map image
set-theoretically into that reduced closure. -/
@[stacks 04Q7] #check
  (AlgebraicGeometry.GroupoidScheme.Hom.reducedImageClosureComposition_range_subset :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {k : Type u} [Field k]
      {G₁ G₂ : AlgebraicGeometry.GroupoidScheme S},
      (eU : AlgebraicGeometry.Spec (CommRingCat.of k) ≅ G₁.U.left) →
      (hU : G₁.U = G₂.U) →
      (f : AlgebraicGeometry.GroupoidScheme.Hom G₁ G₂) →
      (hf : f.IsIdentityOnObjects hU) →
      Set.range
          (AlgebraicGeometry.GroupoidScheme.Hom.reducedImageClosureComposition f).left ⊆
        Set.range
          (AlgebraicGeometry.Scheme.Hom.reducedImageClosureιOver f.arrow).left)
