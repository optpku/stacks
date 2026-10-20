/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.GerbeMorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of gerbe morphisms of fibred categories

Base-change stability is a property of the two local conditions defining a gerbe morphism.  It
does not require the source or target to be a stack, nor does it require groupoid fibers.  For
reflection after a locally essentially surjective base change, only the common target needs
groupoid fibers; the other three categories in the square remain arbitrary fibred categories.
The heterogeneous explicit-construction owners are
`CartesianBasedFunctor.IsGerbeMorphism.cartesianSnd` and
`CartesianBasedFunctor.IsGerbeMorphism.of_cartesianSnd`; the declarations below transport those
facts to arbitrary bicategorical bilimit cones.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Hom.IsGerbeMorphism

variable {J : GrothendieckTopology C}
variable {X Y Y' : FiberedCategoryOver.{u, v, w, vS} C}

/-- Gerbe morphisms of fibred categories are stable under an arbitrary bilimit
pseudopullback. -/
@[stacks 06P3 "base change of gerbe morphisms of fibred categories"]
theorem baseChange
    {F : X ⟶ Y} {G : Y' ⟶ Y}
    (S : Bicategory.PseudoPullbackCone F G) [S.IsBilimit]
    (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism J S.snd := sorry

/-- A morphism of fibred categories with groupoid-fibred target is a gerbe morphism when this
holds after a bilimit pseudopullback along a locally essentially surjective morphism.  No stack
condition or groupoid condition on the source, base-change source, or pullback apex is needed. -/
@[stacks 06P4 "detecting gerbe morphisms after base change"]
theorem ofBaseChange
    {F : X ⟶ Y} {G : Y' ⟶ Y}
    (S : Bicategory.PseudoPullbackCone F G) [S.IsBilimit]
    [Functor.IsFibered.InGroupoids Y.p]
    (hG : FiberedCategoryOver.Hom.LocallyEssentiallySurjective J G)
    (hSsnd : IsGerbeMorphism J S.snd) :
    IsGerbeMorphism J F := sorry

end FiberedCategoryOver.Hom.IsGerbeMorphism

end CategoryTheory
