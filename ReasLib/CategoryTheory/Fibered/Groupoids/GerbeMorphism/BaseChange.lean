module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.GerbeMorphism.BaseChange
public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of gerbe morphisms in groupoid-fibred categories

These theorems specialize the neutral fibred-category base-change API to the groupoid-fibred
bicategory.  In the converse, the neutral theorem only needs the common target to have groupoid
fibers; bundling all four objects in this layer is an application-facing convenience.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism

variable {J : GrothendieckTopology C}
variable {X Y Y' : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- The second projection of a bilimit pseudopullback is a gerbe morphism when the left cospan
leg is one.  This is the groupoid-fibred specialization of the neutral base-change theorem. -/
@[stacks 06P3 "base change in groupoid-fibred categories"]
theorem baseChange
    {F : X ⟶ Y} {G : Y' ⟶ Y}
    (S : Bicategory.PseudoPullbackCone F G) [S.IsBilimit]
    (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism J S.snd := sorry

/-- A morphism of groupoid-fibred categories is a gerbe morphism when this holds after a
bilimit pseudopullback along a locally essentially surjective morphism.  This specializes
`FiberedCategoryOver.Hom.IsGerbeMorphism.ofBaseChange`. -/
@[stacks 06P4 "detecting gerbe morphisms after base change"]
theorem ofBaseChange
    {F : X ⟶ Y} {G : Y' ⟶ Y}
    (S : Bicategory.PseudoPullbackCone F G) [S.IsBilimit]
    (hG : FiberedCategoryOver.Groupoids.Hom.LocallyEssentiallySurjective J G)
    (hSsnd : IsGerbeMorphism J S.snd) :
    IsGerbeMorphism J F := sorry

end FiberedCategoryOver.Groupoids.Hom.IsGerbeMorphism

end CategoryTheory
