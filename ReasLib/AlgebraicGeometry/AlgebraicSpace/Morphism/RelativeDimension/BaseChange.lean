/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-! # Base change of relative dimension and relative-dimension bounds -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A relative-dimension bound on a locally finite type morphism is preserved by base change. -/
instance relativeDimensionLE_pullback_snd {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) (d : ℕ)
    [LocallyOfFiniteType f] [RelativeDimensionLE f d] :
    RelativeDimensionLE (pullback.snd f g) d := sorry

namespace RelativeDimension

/-- Exact relative dimension of a locally finite type morphism is preserved
by base change along an arbitrary morphism. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} {r : ℕ}
    [LocallyOfFiniteType g]
    (sq : IsPullback f' g' g f) (hg : RelativeDimension g r) :
    RelativeDimension g' r :=
  sorry

/-- The first projection from the pullback of a locally finite type morphism
of exact relative dimension `r` has exact relative dimension `r`. -/
theorem pullback_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {g : Z ⟶ Y}
    {r : ℕ} [LocallyOfFiniteType g] (hg : RelativeDimension g r)
    (f : X ⟶ Y) [HasPullback f g] :
    RelativeDimension (pullback.fst f g) r :=
  of_isPullback (IsPullback.of_hasPullback f g).flip hg

end RelativeDimension

/-- The first projection from the pullback of a locally finite type morphism
of exact relative dimension `r` has exact relative dimension `r`. -/
instance relativeDimension_pullback_fst {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y) (r : ℕ)
    [LocallyOfFiniteType g] [RelativeDimension g r] [HasPullback f g] :
    RelativeDimension (pullback.fst f g) r :=
  RelativeDimension.pullback_fst inferInstance f

end AlgebraicGeometry.AlgebraicSpace
