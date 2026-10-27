/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent

/-!
# Smooth descent of local quasi-coherence for étale modules

Local quasi-coherence of an étale module on an algebraic stack is detected by
a jointly point-covering family of smooth morphisms of algebraic stacks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- An étale module on an algebraic stack is locally quasi-coherent if its inverse
images along a jointly point-covering family of smooth morphisms of algebraic
stacks are locally quasi-coherent. -/
@[stacks 075Y]
theorem isLocallyQuasiCoherent_of_smoothCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (h_lqc : ∀ j, IsLocallyQuasiCoherent ((etaleModuleInverseImage (f j)).obj F)) :
    IsLocallyQuasiCoherent F := sorry

/-- An étale module on an algebraic stack is locally quasi-coherent if its inverse
image along a smooth morphism of algebraic stacks surjective on points is locally
quasi-coherent. -/
theorem isLocallyQuasiCoherent_of_smooth_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X) [Smooth f]
    (h_cover : Function.Surjective (Points.map f)) (F : etaleModules X)
    (h_lqc : IsLocallyQuasiCoherent ((etaleModuleInverseImage f).obj F)) :
    IsLocallyQuasiCoherent F := sorry

end AlgebraicGeometry.AlgebraicStack
