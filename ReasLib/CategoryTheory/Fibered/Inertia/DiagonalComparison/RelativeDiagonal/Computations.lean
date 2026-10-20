/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.RelativeDiagonal.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative diagonal computations

This module records the object, morphism, and strict functor projections of the
explicit relative diagonal into its self-pseudo-pullback.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

variable {X Y : BasedCategory C}

/-- The relative diagonal retains the base object of its source object. -/
@[simp, stacks 034H "relative diagonal base object"]
theorem relativeDiagonal.obj.base (F : X ⥤ᵇ Y) (x : X.obj) :
    PseudoPullback.baseObj ((relativeDiagonal F).obj x) = X.p.obj x := sorry
/- Proof strategy: unfold `relativeDiagonal` through its private constructor and read the public
`PseudoPullback.baseObj` projection. -/

/-- The first object projection of the relative diagonal is the original object. -/
@[simp, stacks 034H "relative diagonal first object"]
theorem relativeDiagonal.obj.fst (F : X ⥤ᵇ Y) (x : X.obj) :
    PseudoPullback.fstObj ((relativeDiagonal F).obj x) = x := sorry
/- Proof strategy: unfold only the public owner and use the first object projection of
`PseudoPullback.mk`. -/

/-- The second object projection of the relative diagonal is the original object. -/
@[simp, stacks 034H "relative diagonal second object"]
theorem relativeDiagonal.obj.snd (F : X ⥤ᵇ Y) (x : X.obj) :
    PseudoPullback.sndObj ((relativeDiagonal F).obj x) = x := sorry
/- Proof strategy: unfold only the public owner and use the second object projection of
`PseudoPullback.mk`. -/

/-- The comparison carried by a relative-diagonal object is the identity. -/
@[simp, stacks 034H "relative diagonal comparison component"]
theorem relativeDiagonal.obj.comparison (F : X ⥤ᵇ Y) (x : X.obj) :
    PseudoPullback.comparison ((relativeDiagonal F).obj x) = 𝟙 (F.obj x) := sorry
/- Proof strategy: expose the comparison projection of the public pseudo-pullback object; its
private construction uses the identity fiber isomorphism. -/

/-- The objectwise comparison isomorphism of a relative-diagonal object is the identity
isomorphism. This exposes both directions of the canonical comparison without requiring consumers
to unfold `PseudoPullback.comparisonIsoApp`. -/
@[simp, stacks 034H "relative diagonal comparison isomorphism"]
theorem relativeDiagonal.obj.comparisonIso (F : X ⥤ᵇ Y) (x : X.obj) :
    PseudoPullback.comparisonIsoApp ((relativeDiagonal F).obj x) = Iso.refl (F.obj x) := sorry

/-- The forward component of a relative-diagonal comparison is the identity. -/
@[simp, stacks 034H "relative diagonal comparison isomorphism hom"]
theorem relativeDiagonal.obj.comparisonIso.hom (F : X ⥤ᵇ Y) (x : X.obj) :
    (PseudoPullback.comparisonIsoApp ((relativeDiagonal F).obj x)).hom =
      𝟙 (F.obj x) := sorry

/-- The inverse component of a relative-diagonal comparison is the identity. -/
@[simp, stacks 034H "relative diagonal comparison isomorphism inverse"]
theorem relativeDiagonal.obj.comparisonIso.inv (F : X ⥤ᵇ Y) (x : X.obj) :
    (PseudoPullback.comparisonIsoApp ((relativeDiagonal F).obj x)).inv =
      𝟙 (F.obj x) := sorry

/-- The common base map of the relative diagonal is the image under the source projection. -/
@[simp, stacks 034H "relative diagonal base map"]
theorem relativeDiagonal.map.base (F : X ⥤ᵇ Y) {x y : X.obj} (f : x ⟶ y) :
    PseudoPullback.baseMap ((relativeDiagonal F).map f) = X.p.map f := sorry
/- Proof strategy: unfold the public owner and read the common base-map projection of
`PseudoPullback.Hom.mk`. -/

/-- The first morphism projection of the relative diagonal is the original morphism. -/
@[simp, stacks 034H "relative diagonal first map"]
theorem relativeDiagonal.map.fst (F : X ⥤ᵇ Y) {x y : X.obj} (f : x ⟶ y) :
    PseudoPullback.fstMap ((relativeDiagonal F).map f) = f := sorry
/- Proof strategy: unfold the public owner and read the first map projection of
`PseudoPullback.Hom.mk`. -/

/-- The second morphism projection of the relative diagonal is the original morphism. -/
@[simp, stacks 034H "relative diagonal second map"]
theorem relativeDiagonal.map.snd (F : X ⥤ᵇ Y) {x y : X.obj} (f : x ⟶ y) :
    PseudoPullback.sndMap ((relativeDiagonal F).map f) = f := sorry
/- Proof strategy: unfold the public owner and read the second map projection of
`PseudoPullback.Hom.mk`. -/

/-- A relative-diagonal morphism satisfies the comparison square of its two identical legs. -/
@[stacks 034H "relative diagonal map square"]
theorem relativeDiagonal.map.comm (F : X ⥤ᵇ Y) {x y : X.obj} (f : x ⟶ y) :
    CommSq
      (F.toFunctor.map f)
      (PseudoPullback.comparison ((relativeDiagonal F).obj x))
      (PseudoPullback.comparison ((relativeDiagonal F).obj y))
      (F.toFunctor.map f) := sorry

/-- The comparison arrows of relative-diagonal objects are natural in source morphisms. -/
@[reassoc, stacks 034H "relative diagonal map naturality"]
theorem relativeDiagonal.map.naturality (F : X ⥤ᵇ Y) {x y : X.obj} (f : x ⟶ y) :
    F.toFunctor.map f ≫
        PseudoPullback.comparison ((relativeDiagonal F).obj y) =
      PseudoPullback.comparison ((relativeDiagonal F).obj x) ≫ F.toFunctor.map f := sorry

/-- The first projection of the relative diagonal is the identity based functor. -/
@[simp, stacks 034H "relative diagonal first projection"]
theorem relativeDiagonal.fst (F : X ⥤ᵇ Y) :
    relativeDiagonal F ⋙ PseudoPullback.fst F F = 𝟭 X := sorry

/-- The second projection of the relative diagonal is the identity based functor. -/
@[simp, stacks 034H "relative diagonal second projection"]
theorem relativeDiagonal.snd (F : X ⥤ᵇ Y) :
    relativeDiagonal F ⋙ PseudoPullback.snd F F = 𝟭 X := sorry

end BasedFunctor

end CategoryTheory
