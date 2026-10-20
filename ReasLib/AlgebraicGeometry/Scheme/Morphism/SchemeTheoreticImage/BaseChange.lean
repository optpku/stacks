/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Comma.Over.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Formation of the scheme-theoretic image of a relative morphism commutes with every base
change when the image after pullback is defined by the pulled-back kernel ideal sheaf. -/
def ImageCommutesWithBaseChange {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) : Prop :=
  ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
    Scheme.Hom.image (((Over.pullback g).map f).left) =
      (f.left.ker.comap (pullback.fst Y.hom g)).subscheme

/-- The image-base-change property expands to the equality of the pulled-back image with the
closed subscheme defined by the inverse-image kernel ideal after every base change. -/
theorem imageCommutesWithBaseChange_iff {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    ImageCommutesWithBaseChange f ↔
      ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
        Scheme.Hom.image (((Over.pullback g).map f).left) =
          (f.left.ker.comap (pullback.fst Y.hom g)).subscheme := sorry

/-- An image-base-change hypothesis gives the scheme-theoretic-image equality for a specified
base change. -/
theorem ImageCommutesWithBaseChange.image_eq {S S' : Scheme.{u}} {X Y : Over S}
    {f : X ⟶ Y} (h : ImageCommutesWithBaseChange f) (g : S' ⟶ S) :
    Scheme.Hom.image (((Over.pullback g).map f).left) =
      (f.left.ker.comap (pullback.fst Y.hom g)).subscheme := sorry

end AlgebraicGeometry.Scheme.Hom
