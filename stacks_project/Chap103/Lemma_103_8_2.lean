/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.FlatBaseChange.Descent
import StacksCheckRecall

/-!
# Detection of `LQCoh^{fbc}` on a covering of algebraic stacks

On an algebraic stack, membership of a module in `LQCoh^{fbc}(𝒪_X)` is detected
on a jointly point-covering family: a smooth family for étale modules, and a
flat and locally finitely presented family for fppf modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

/- Lemma 103.8.2 (1): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a family
of smooth morphisms of algebraic stacks with `|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a
sheaf of `𝒪_X`-modules on `X_étale`. If each inverse image
`(etaleModuleInverseImage (f j)).obj F` lies in `LQCoh^{fbc}(𝒪_{Xj j})`, then `F` lies in
`LQCoh^{fbc}(𝒪_X)`. The printed source token `LQCoh^{fpc}` denotes this same class,
detected by combining Lemma 103.6.1 and Lemma 103.7.2. The source index `i` in
the membership condition is read as `j`, matching the covering family. -/
@[stacks 07AQ] #check
  (AlgebraicGeometry.AlgebraicStack.lqcohFbc_of_smoothCovering :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (_ : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (_ : ∀ j, lqcohFbc (Xj j) ((etaleModuleInverseImage (f j)).obj F)),
    lqcohFbc X F)

/- If `f : Y ⟶ X` is a smooth morphism of algebraic stacks which is surjective on
points, then an étale `𝒪_X`-module lies in `LQCoh^{fbc}` as soon as its inverse
image along `f` does. -/
#check (AlgebraicGeometry.AlgebraicStack.lqcohFbc_of_smooth_pointsSurjective :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X) [Smooth f]
    (_ : Function.Surjective (Points.map f)) (F : etaleModules X)
    (_ : lqcohFbc Y ((etaleModuleInverseImage f).obj F)),
    lqcohFbc X F)

/- Lemma 103.8.2 (2): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a family
of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_fppf`. If each
inverse image `(modulePullback (f j)).obj F` lies in `LQCoh^{fbc}(𝒪_{Xj j})`, then
`F` lies in `LQCoh^{fbc}(𝒪_X)`. The source index `i` in the membership condition
is read as `j`, matching the covering family. -/
@[stacks 07AQ] #check
  (AlgebraicGeometry.AlgebraicStack.lqcohFbc_of_fppfCovering :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)] [∀ j, LocallyOfFinitePresentation (f j)]
    (_ : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : fppfModules X)
    (_ : ∀ j, FppfModules.lqcohFbc (Xj j) ((modulePullback (f j)).obj F)),
    FppfModules.lqcohFbc X F)

/- If `f : Y ⟶ X` is a flat and locally finitely presented morphism of algebraic
stacks which is surjective on points, then an fppf `𝒪_X`-module lies in
`LQCoh^{fbc}` as soon as its inverse image along `f` does. -/
#check (AlgebraicGeometry.AlgebraicStack.lqcohFbc_of_fppf_pointsSurjective :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f]
    (_ : Function.Surjective (Points.map f))
    (F : fppfModules X)
    (_ : FppfModules.lqcohFbc Y ((modulePullback f).obj F)),
    FppfModules.lqcohFbc X F)
