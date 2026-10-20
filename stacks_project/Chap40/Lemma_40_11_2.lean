/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.Range

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 40.11.2: in the setup of Situation 40.11.1, if the image of the arrow morphism
is open, then it is closed. -/
@[stacks 04Q6] #check
  (AlgebraicGeometry.GroupoidScheme.Hom.isClosed_range_of_isOpen :
    ∀ {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
      (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
      (f : GroupoidScheme.Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU),
      IsOpen (Set.range f.arrow.left) → IsClosed (Set.range f.arrow.left))
