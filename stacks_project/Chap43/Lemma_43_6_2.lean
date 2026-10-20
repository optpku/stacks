/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.Pushforward.Composition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 43.6.2: for proper morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of varieties,
successive proper pushforward on degree-`k` cycles equals pushforward along `f ≫ g`. -/
@[stacks 0B0N] #check
  (AlgebraicGeometry.CycleGroup.mapHom_comp_of_proper_over_field :
    ∀ {K : Type u} [Field K]
      (X Y Z : SchemeOverField K) [Variety X] [Variety Y] [Variety Z]
      (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left] [IsProper g.left] (k : ℤ),
      (CycleGroup.mapHom g.left
        (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (Z.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k).comp
          (CycleGroup.mapHom f.left
            (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
            (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k) =
        CycleGroup.mapHom (f.left ≫ g.left)
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
          (Z.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k)
