/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap70.Lemma_70_19_3_FinitePresentationIsoOverOpen
public import stacks_project.Chap70.Lemma_70_19_3_Henselization

/-!
# Base change to the punctured henselization of a decent algebraic space

Slice base change along `fromHenselization` lifts to finite-presentation
iso-over-open slice categories, from the complement of a closed point to the
punctured spectrum of the henselization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Base change along `fromHenselization` preserves finite presentation and being an
isomorphism over the complementary open of a closed point, after restriction to
the punctured henselization. -/
theorem puncturedHenselizationBaseChange_mem {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)]
    (Y : FinitePresentationIsoOverOpen (closedPointComplementι X hx)) :
    finitePresentationIsoOverOpenProperty (henselizationPuncturedι X x)
      ((overPullback (fromHenselization X x)).obj Y.obj) :=
  sorry

/-- Base change along `Spec(𝒪_{X,x}^h) ⟶ X` as a functor on finite-presentation
iso-over-open slice categories, from `X \ {x}` to the punctured henselization. -/
def puncturedHenselizationBaseChange {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] {x : Points X} (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)] :
    FinitePresentationIsoOverOpen (closedPointComplementι X hx) ⥤
      FinitePresentationIsoOverOpen (henselizationPuncturedι X x) :=
  ObjectProperty.lift
    (finitePresentationIsoOverOpenProperty (henselizationPuncturedι X x))
    (FinitePresentationIsoOverOpen.inclusion (closedPointComplementι X hx) ⋙
      overPullback (fromHenselization X x))
    (fun Y ↦ puncturedHenselizationBaseChange_mem X hx Y)

/-- The structure morphism of a `puncturedHenselizationBaseChange` object is the
second projection of the fibre product along `fromHenselization`. -/
theorem puncturedHenselizationBaseChange_obj_hom {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X))
    [QuasiCompact (closedPointComplementι X hx)]
    (Y : FinitePresentationIsoOverOpen (closedPointComplementι X hx)) :
    ((puncturedHenselizationBaseChange X hx).obj Y).obj.hom =
      overPullbackSnd (fromHenselization X x) Y.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
