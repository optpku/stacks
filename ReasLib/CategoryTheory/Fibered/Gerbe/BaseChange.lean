/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.GerbeMorphism.BaseChange
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism.BaseChange
public import ReasLib.CategoryTheory.Fibered.Gerbe.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of relative gerbes

The canonical base-change owners live at the neutral fibred-category and groupoid-fibred layers.
This module records their thin specializations to relative gerbes of stacks in groupoids.  All
versions use an arbitrary bilimit pseudopullback cone, so consumers do not need to choose a
particular two-fibre-product presentation.

## Main declarations

* `FiberedCategoryOver.Hom.IsGerbeMorphism.baseChange` — the neutral forward theorem.
* `FiberedCategoryOver.Hom.IsGerbeMorphism.ofBaseChange` — neutral reflection with only a
  groupoid-fibred common target.
* `CartesianBasedFunctor.IsGerbeMorphism.cartesianSnd` and
  `CartesianBasedFunctor.IsGerbeMorphism.of_cartesianSnd` — heterogeneous owners for the explicit
  pseudo-pullback construction.
* `FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism.ofBaseChange` — the fully groupoid-fibred
  specialization.
* `StackOver.Groupoids.Hom.IsGerbeMorphism.baseChange` and
  `StackOver.Groupoids.Hom.IsGerbeMorphism.ofBaseChange` — stack specializations.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

namespace StackOver.Groupoids.Hom.IsGerbeMorphism

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Y' : StackOver.Groupoids J}

/-- Lemma 8.11.5: in a bilimit pseudopullback square of stacks in groupoids, the projection to
the changed base is a relative gerbe whenever the original right-hand map is one.  This is the
stack specialization of `FiberedCategoryOver.Hom.IsGerbeMorphism.baseChange`. -/
@[stacks 06P3]
theorem baseChange
    {F : X ⟶ Y} {G : Y' ⟶ Y}
    (S : Bicategory.PseudoPullbackCone F G) [S.IsBilimit]
    (hF : StackOver.Groupoids.Hom.IsGerbeMorphism F) :
    StackOver.Groupoids.Hom.IsGerbeMorphism S.snd := sorry

/-- Lemma 8.11.7: a relative gerbe can be detected after a bilimit pseudopullback base change
whose base-change map is locally essentially surjective on fiber objects.  This specializes
`FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism.ofBaseChange`; the groupoid-fibre hypothesis is
provided by the bundled stack objects. -/
@[stacks 06P4]
theorem ofBaseChange
    {F : X ⟶ Y} {G : Y' ⟶ Y}
    (S : Bicategory.PseudoPullbackCone F G) [S.IsBilimit]
    (hG : StackOver.Groupoids.Hom.LocallyEssentiallySurjective G)
    (hSsnd : StackOver.Groupoids.Hom.IsGerbeMorphism S.snd) :
    StackOver.Groupoids.Hom.IsGerbeMorphism F := sorry

end StackOver.Groupoids.Hom.IsGerbeMorphism

end CategoryTheory
