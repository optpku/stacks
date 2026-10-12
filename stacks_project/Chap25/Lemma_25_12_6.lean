/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Finite
import StacksCheckRecall

universe w v u

namespace CategoryTheory

open Limits
open SemiRepresentableFamily
open scoped CategoryTheory.SemiRepresentableFamily

open SemiRepresentableFamily.OverFamily

/- Lemma 25.12.6 (094K): a site with pullbacks and enough finite `B`-valued covering families
admits a hypercovering lying degreewise in `B` with finite degree indices, provided these covers
remain covering after adjoining one arrow from an object of `B`. -/
@[stacks 094K]
#check (@Hypercovering.exists_degreewiseFiniteIn :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : OverFamily.{v, u, w} U, 𝒰.IsFiniteBasisCovering J B)
    (hadd : ∀ {U : C} (𝒰 : OverFamily.{v, u, w} U)
      (h𝒰 : 𝒰.IsFiniteBasisCovering J B)
      {U' : C} (f : U' ⟶ U) (hU' : U' ∈ B), (𝒰.addSingleton f).toSieve ∈ J U)
    (X : C),
    ∃ K : Hypercovering.{w} J X, K.degreewiseObjectsIn B ∧ K.degreewiseFinite)

/- Degreewise finiteness is consumed at an arbitrary degree; zero, one, and successor degrees
are lightweight specializations rather than separate existence statements. -/
#check @Hypercovering.degreewiseFinite.finite
#check @Hypercovering.degreewiseFinite.zero
#check @Hypercovering.degreewiseFinite.one
#check @Hypercovering.degreewiseFinite.succ

/- The finite-family owner exposes the single-arrow closure step independently. -/
#check @Limits.FormalCoproduct.IsFiniteBasisCovering.addSingleton

end CategoryTheory
