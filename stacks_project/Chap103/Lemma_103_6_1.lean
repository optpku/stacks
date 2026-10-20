/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-!
# Detection of local quasi-coherence on a smooth covering of algebraic stacks

On an algebraic stack, local quasi-coherence of an étale module is detected
on a jointly point-covering family of smooth morphisms of algebraic stacks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Lemma 103.6.1: let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a family
of smooth morphisms of algebraic stacks with `|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a
sheaf of `𝒪_X`-modules on `X_étale`. If each inverse image
`(moduleInverseImage (f j)).obj F` is locally quasi-coherent, then so is `F`. -/
@[stacks 075Y]
theorem isLocallyQuasiCoherent_of_smoothCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (h_lqc : ∀ j, IsLocallyQuasiCoherent ((moduleInverseImage (f j)).obj F)) :
    IsLocallyQuasiCoherent F :=
  sorry

/-- If `f : Y ⟶ X` is a smooth morphism of algebraic stacks which is surjective on
points, then an étale `𝒪_X`-module is locally quasi-coherent as soon as its inverse
image along `f` is. -/
theorem isLocallyQuasiCoherent_of_smooth_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X) [Smooth f]
    (h_cover : Function.Surjective (Points.map f)) (F : etaleModules X)
    (h_lqc : IsLocallyQuasiCoherent ((moduleInverseImage f).obj F)) :
    IsLocallyQuasiCoherent F :=
  sorry

end AlgebraicGeometry.AlgebraicStack
