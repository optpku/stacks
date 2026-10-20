/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations.FormallySmooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 98.13.6 (1): if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
formally smooth on objects, then `f` satisfies (98.13.2.1). -/
@[stacks 07XW] #check
  (AlgebraicGeometry.Groupoids.Hom.IsSmoothOnPredeformations.of_formallySmoothOnObjects :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
      (f : X ⟶ Y) [FormallySmoothOnObjects f], IsSmoothOnPredeformations f)

/- Lemma 98.13.6 (2): if `S` is locally Noetherian and `f : X ⟶ Y` is a
1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces and smooth, then `f` satisfies (98.13.2.1). -/
@[stacks 07XW] #check
  (AlgebraicGeometry.Groupoids.Hom.IsSmoothOnPredeformations.of_smooth :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
      (f : X ⟶ Y) [Smooth f], IsSmoothOnPredeformations f)
