module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

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

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Lemma 103.8.2 (1): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a family
of smooth morphisms of algebraic stacks with `|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a
sheaf of `𝒪_X`-modules on `X_étale`. If each inverse image
`(moduleInverseImage (f j)).obj F` lies in `LQCoh^{fbc}(𝒪_{Xj j})`, then `F` lies in
`LQCoh^{fbc}(𝒪_X)`. The printed source token `LQCoh^{fpc}` denotes this same class,
detected by combining Lemma 103.6.1 and Lemma 103.7.2. -/
@[stacks 07AQ]
theorem lqcohFbc_of_smoothCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (h_fbc : ∀ j, lqcohFbc (Xj j) ((moduleInverseImage (f j)).obj F)) :
    lqcohFbc X F :=
  sorry

/-- If `f : Y ⟶ X` is a smooth morphism of algebraic stacks which is surjective on
points, then an étale `𝒪_X`-module lies in `LQCoh^{fbc}` as soon as its inverse
image along `f` does. -/
theorem lqcohFbc_of_smooth_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X) [Smooth f]
    (h_cover : Function.Surjective (Points.map f)) (F : etaleModules X)
    (h_fbc : lqcohFbc Y ((moduleInverseImage f).obj F)) :
    lqcohFbc X F :=
  sorry

/-- Lemma 103.8.2 (2): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a family
of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_fppf`. If each
inverse image `(modulePullback (f j)).obj F` lies in `LQCoh^{fbc}(𝒪_{Xj j})`, then
`F` lies in `LQCoh^{fbc}(𝒪_X)`. -/
@[stacks 07AQ]
theorem lqcohFbc_of_fppfCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)] [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : fppfModules X)
    (h_fbc : ∀ j, FppfModules.lqcohFbc (Xj j) ((modulePullback (f j)).obj F)) :
    FppfModules.lqcohFbc X F :=
  sorry

/-- If `f : Y ⟶ X` is a flat and locally finitely presented morphism of algebraic
stacks which is surjective on points, then an fppf `𝒪_X`-module lies in
`LQCoh^{fbc}` as soon as its inverse image along `f` does. -/
theorem lqcohFbc_of_fppf_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f]
    (h_cover : Function.Surjective (Points.map f))
    (F : fppfModules X)
    (h_fbc : FppfModules.lqcohFbc Y ((modulePullback f).obj F)) :
    FppfModules.lqcohFbc X F :=
  sorry

end AlgebraicGeometry.AlgebraicStack
