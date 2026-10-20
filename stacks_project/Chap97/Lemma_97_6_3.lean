/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects.Representable
import StacksCheckRecall

/-!
# Formal smoothness on objects versus formal smoothness

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is formally smooth on objects if and only if
it is formally smooth in the sense of Algebraic Stacks, Definition 94.10.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 97.6.3: Let `p : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `p` is representable by algebraic spaces,
then `p` is formally smooth on objects if and only if `p` is formally smooth
in the sense of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 06D3] #check (AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects.iff_has :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y}
    (hp : relativelyRepresentableByAlgebraicSpaces p),
    FormallySmoothOnObjects p ↔ has (@AlgebraicSpace.FormallySmooth S) p)

end AlgebraicGeometry.Groupoids.Hom
