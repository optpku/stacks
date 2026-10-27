/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage

/-!
# Descent of locally quasi-coherent modules with flat base change

Membership in `LQCoh^{fbc}` is detected on jointly point-covering smooth families
for étale modules and on jointly point-covering flat, locally finitely presented
families for fppf modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- An étale module on an algebraic stack is locally quasi-coherent with flat
base change if its inverse images along a jointly point-covering family of
smooth morphisms of algebraic stacks have these properties. -/
theorem lqcohFbc_of_smoothCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (h_fbc : ∀ j, lqcohFbc (Xj j) ((etaleModuleInverseImage (f j)).obj F)) :
    lqcohFbc X F := sorry

/-- An étale module on an algebraic stack is locally quasi-coherent with flat
base change if its inverse image along a smooth morphism of algebraic stacks
which is surjective on points has these properties. -/
theorem lqcohFbc_of_smooth_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X) [Smooth f]
    (h_cover : Function.Surjective (Points.map f)) (F : etaleModules X)
    (h_fbc : lqcohFbc Y ((etaleModuleInverseImage f).obj F)) :
    lqcohFbc X F := sorry

/-- An fppf module on an algebraic stack is locally quasi-coherent with flat
base change if its inverse images along a jointly point-covering family of flat,
locally finitely presented morphisms of algebraic stacks have these properties. -/
theorem lqcohFbc_of_fppfCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)] [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : fppfModules X)
    (h_fbc : ∀ j, FppfModules.lqcohFbc (Xj j) ((modulePullback (f j)).obj F)) :
    FppfModules.lqcohFbc X F := sorry

/-- An fppf module on an algebraic stack is locally quasi-coherent with flat
base change if its inverse image along a flat, locally finitely presented
morphism of algebraic stacks which is surjective on points has these properties. -/
theorem lqcohFbc_of_fppf_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f]
    (h_cover : Function.Surjective (Points.map f))
    (F : fppfModules X)
    (h_fbc : FppfModules.lqcohFbc Y ((modulePullback f).obj F)) :
    FppfModules.lqcohFbc X F := sorry

end AlgebraicGeometry.AlgebraicStack
