/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
import Mathlib.Tactic.CrossRefAttribute

/-!
# Images of site-level hypercoverings

This leaf maps a hypercovering of the terminal presheaf degreewise along a morphism of sites
which preserves equalizers and pullbacks.
-/

@[expose] public section

noncomputable section

universe w vC vD u₁ u₂

namespace CategoryTheory

open Limits
open scoped CategoryTheory.SemiRepresentableFamily

namespace HypercoveringOf.Terminal

variable {C : Type u₁} [Category.{vC} C]
variable {D : Type u₂} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasEqualizers C] [HasPullbacks C]
variable [HasEqualizers D] [HasPullbacks D]

/-- Apply a functor degreewise to the simplicial semi-representable family underlying a
site-level hypercovering. -/
abbrev mapSimplicial (u : D ⥤ C) (K : HypercoveringOf.Terminal.{w} JD) :
    SimplicialObject (SR(C)) :=
  K.simplicial ⋙ SemiRepresentableFamily.map u

/-- Each degree of `mapSimplicial` is the image of the corresponding semi-representable family. -/
@[simp] theorem mapSimplicial_obj
    (u : D ⥤ C) (K : HypercoveringOf.Terminal.{w} JD)
    (Δ : SimplexCategoryᵒᵖ) :
    (mapSimplicial u K).obj Δ =
      (SemiRepresentableFamily.map u).obj (K.simplicial.obj Δ) := sorry

/-- The degree-zero local-surjectivity condition is preserved by a morphism of sites which
preserves equalizers and pullbacks. -/
theorem map_zeroLocallySurjective
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal.{w} JD) :
    ZeroLocallySurjective JC (mapSimplicial u K) := sorry

/-- The degree-one local-surjectivity condition is preserved by a morphism of sites which
preserves equalizers and pullbacks. -/
theorem map_oneLocallySurjective
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal.{w} JD) :
    OneLocallySurjective JC (mapSimplicial u K) := sorry

/-- Every higher local-surjectivity condition is preserved by a morphism of sites which
preserves equalizers and pullbacks. -/
theorem map_higherLocallySurjective
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal.{w} JD) (n : ℕ) :
    HigherLocallySurjective JC (mapSimplicial u K) (n + 1) := sorry

/-- Lemma 25.12.4 (0DAY): apply a finite-limit-preserving morphism of sites degreewise to a
site-level hypercovering. -/
@[stacks 0DAY "image of a site-level hypercovering"]
def map
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal.{w} JD) :
    HypercoveringOf.Terminal.{w} JC :=
  ofSimplicial JC (mapSimplicial u K)
    (map_zeroLocallySurjective u K)
    (map_oneLocallySurjective u K)
    (fun n ↦ map_higherLocallySurjective u K n)

/-- The underlying simplicial object of `map` is obtained by applying the functor degreewise. -/
@[simp] theorem map_simplicial
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [PreservesLimitsOfShape WalkingCospan u]
    (K : HypercoveringOf.Terminal.{w} JD) :
    (map (JC := JC) u K).simplicial = mapSimplicial u K := sorry

end HypercoveringOf.Terminal
end CategoryTheory
