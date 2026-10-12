/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.Family.Overlap
public import ReasLib.CategoryTheory.Sites.Family.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent along a local refinement

A refinement from a fine family `𝒱` to a coarse family `𝒰` lets one reconstruct descent
for `𝒰` from descent for `𝒱` when descent on the restrictions of `𝒱` to every member of `𝒰`
is fully faithful and descent on pairwise overlaps is faithful.

Unlike an unrestricted refinement statement, the local hypotheses below are essential: an
arbitrary family morphism need not induce a full or faithful pullback functor on descent data.

## Main declarations

* `DescentDatum.Refinement.pullFunctor_faithful` - local faithfulness gives a faithful refinement
  functor.
* `DescentDatum.Refinement.pullFunctor_full` - member and overlap hypotheses give a full refinement
  functor.
* `DescentDatum.Refinement.canonicalFunctor_isEquivalence` - effective descent descends from the
  fine family to the coarse family.
-/

@[expose] public section

universe w uC uS vC vS

namespace CategoryTheory

open Limits

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {p : S ⥤ C}
variable (hc : Functor.Cleavage p)
variable {U : C}

namespace DescentDatum

open SemiRepresentableFamily.Over

namespace Refinement

/-- Pullback on descent data along a refinement is faithful when the canonical descent functor on
the restriction of the fine family to every coarse member is faithful. -/
@[stacks 0GEA "faithfulness of descent pullback along a local refinement"]
theorem pullFunctor_faithful
    {𝒰 𝒱 : SemiRepresentableFamily.Over.{w} U}
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i : 𝒰.index,
      Functor.Faithful (canonicalFunctor hc (𝒱.baseChange (𝒰.obj i).hom))]
    (φ : 𝒱 ⟶ 𝒰) :
    Functor.Faithful (DescentDatum.Pullback.functorOfRefinement hc φ) := sorry

/-- Pullback on descent data along a refinement is full when descent is fully faithful on every
coarse member and faithful on every pairwise overlap. -/
@[stacks 0GEA "fullness of descent pullback along a local refinement"]
theorem pullFunctor_full
    {𝒰 𝒱 : SemiRepresentableFamily.Over.{w} U}
    [𝒰.toPresieve.HasPairwisePullbacks]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.overlapMap i i')]
    [∀ i : 𝒰.index,
      Functor.Full (canonicalFunctor hc (𝒱.baseChange (𝒰.obj i).hom))]
    [∀ i : 𝒰.index,
      Functor.Faithful (canonicalFunctor hc (𝒱.baseChange (𝒰.obj i).hom))]
    [∀ i i' : 𝒰.index,
      Functor.Faithful (canonicalFunctor hc (𝒱.baseChange (𝒰.overlapMap i i')))]
    (φ : 𝒱 ⟶ 𝒰) :
    Functor.Full (DescentDatum.Pullback.functorOfRefinement hc φ) := sorry

/-- Lemma 8.3.7 (tag 0GEA): let `𝒱` refine `𝒰`. If descent for `𝒱` is effective,
descent on its restriction to every member of `𝒰` is fully faithful, and descent on its
restriction to every pairwise overlap of `𝒰` is faithful, then descent for `𝒰` is effective. -/
@[stacks 0GEA "effective descent along a local refinement"]
theorem canonicalFunctor_isEquivalence
    {𝒰 𝒱 : SemiRepresentableFamily.Over.{w} U}
    [𝒰.toPresieve.HasPairwisePullbacks]
    [∀ i : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.obj i).hom]
    [∀ i i' : 𝒰.index, ∀ j : 𝒱.index,
      HasPullback (𝒱.obj j).hom (𝒰.overlapMap i i')]
    [∀ i : 𝒰.index,
      Functor.Full (canonicalFunctor hc (𝒱.baseChange (𝒰.obj i).hom))]
    [∀ i : 𝒰.index,
      Functor.Faithful (canonicalFunctor hc (𝒱.baseChange (𝒰.obj i).hom))]
    [∀ i i' : 𝒰.index,
      Functor.Faithful (canonicalFunctor hc (𝒱.baseChange (𝒰.overlapMap i i')))]
    (φ : 𝒱 ⟶ 𝒰) [Functor.IsEquivalence (canonicalFunctor hc 𝒱)] :
    Functor.IsEquivalence (canonicalFunctor hc 𝒰) := sorry

end Refinement

end DescentDatum

end CategoryTheory
