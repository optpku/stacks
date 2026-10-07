module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Images of hypercoverings under continuous functors

This leaf owns the degreewise image construction for fixed-target formal-coproduct
hypercoverings.  The covering assertions are stated separately so applications can
reuse the simplicial object and its matching-map computations independently.
-/

@[expose] public section

noncomputable section

universe w vC vD u₁ u₂

namespace CategoryTheory

open Opposite
open Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u₁} [Category.{vC} C]
variable {D : Type u₂} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasPullbacks C] [HasPullbacks D]

namespace Functor.Hypercovering

open SemiRepresentableFamily.OverFamily

/-- Applying `u` degreewise to the simplicial fixed-target family underlying a hypercovering of
`Y`. -/
abbrev simplicial
    (u : D ⥤ C) {Y : D} (K : CategoryTheory.Hypercovering.{w} JD Y) :
    SimplicialObject (SR(C, u.obj Y)) :=
  K.toSimplicialObject ⋙ SemiRepresentableFamily.map (Over.post u)

/-- Each degree of `Functor.Hypercovering.simplicial` is the image of the corresponding
fixed-target formal-coproduct family under `SemiRepresentableFamily.map (Over.post u)`. -/
theorem simplicial_obj
    (u : D ⥤ C) {Y : D} (K : CategoryTheory.Hypercovering.{w} JD Y)
    (Δ : SimplexCategoryᵒᵖ) :
    (simplicial u K).obj Δ =
      (SemiRepresentableFamily.map (Over.post u)).obj (K.toSimplicialObject.obj Δ) := sorry

/-- The degree-zero family of the degreewise image is covering when `u` is continuous and
preserves pullbacks. -/
theorem zero_isCovering
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : CategoryTheory.Hypercovering.{w} JD Y) :
    ((simplicial u K).obj (op <| SimplexCategory.mk 0)).toSieve ∈
      JC (u.obj Y) := sorry

/-- Every matching map of the degreewise image is covering when `u` is continuous and
preserves pullbacks. -/
theorem succ_isCovering
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : CategoryTheory.Hypercovering.{w} JD Y) (n : ℕ) :
    SemiRepresentableFamily.OverFamily.covering JC
      (SimplicialObject.matchingMap (simplicial u K) n) := sorry

/-- Lemma 25.12.5 (0DAZ): the hypercovering of `u.obj Y` obtained by applying a continuous
pullback-preserving functor degreewise to a hypercovering of `Y`. -/
@[stacks 0DAZ "image of a hypercovering"]
noncomputable def map
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : CategoryTheory.Hypercovering.{w} JD Y) :
    CategoryTheory.Hypercovering.{w} JC (u.obj Y) where
  toSimplicialObject := simplicial u K
  zero_isCovering := zero_isCovering u K
  succ_isCovering n := succ_isCovering u K n

/-- The simplicial object underlying `Functor.Hypercovering.map` is its degreewise image. -/
@[simp]
theorem map_toSimplicialObject
    (u : D ⥤ C) [u.IsContinuous JD JC]
    [PreservesLimitsOfShape WalkingCospan u]
    {Y : D} (K : CategoryTheory.Hypercovering.{w} JD Y) :
    (map (JD := JD) (JC := JC) u K).toSimplicialObject =
      simplicial (JD := JD) u K := sorry

end Functor.Hypercovering

end CategoryTheory
