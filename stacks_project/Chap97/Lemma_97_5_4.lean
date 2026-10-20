/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects.OpenImmersion
import StacksCheckRecall

/-!
# Open immersions are limit preserving on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces and an open immersion is limit preserving
on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LimitPreservingOnObjects

/- Lemma 97.5.4: Let `p : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. Assume `p` is representable by algebraic spaces
and an open immersion. Then `p` is limit preserving on objects. -/
@[stacks 06CY] #check
  (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.of_openImmersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
      [AlgebraicGeometry.Groupoids.Hom.OpenImmersion p],
      AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects p)

end LimitPreservingOnObjects

end AlgebraicGeometry.Groupoids.Hom
