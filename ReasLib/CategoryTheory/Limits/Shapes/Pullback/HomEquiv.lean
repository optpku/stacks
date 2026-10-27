/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 016U

# Hom equivalences for pullbacks

This file packages the universal property of a pullback as an equivalence with compatible pairs of
morphisms. The forward and inverse maps are explicit, so downstream users do not need to pass
through `Type`-valued pullbacks, Yoneda, or concrete-category encodings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

namespace pullback

variable {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]

/-- A compatible pair of morphisms from `T` to the two objects over `Z`. -/
@[stacks 016U "compatible morphism pairs for pullbacks",
  stacks 0173 "compatible morphism pairs for pullbacks"]
abbrev CompatiblePair (T : C) :=
  { p : (T ⟶ X) × (T ⟶ Y) // p.1 ≫ f = p.2 ≫ g }

namespace CompatiblePair

/-- Precomposition preserves the compatibility equation for a pullback pair. -/
@[stacks 016U "precomposition of compatible pullback pairs",
  stacks 0173 "precomposition of compatible pullback pairs"]
theorem precomp_condition {S T : C} (k : S ⟶ T) (p : CompatiblePair f g T) :
    (k ≫ p.1.1) ≫ f = (k ≫ p.1.2) ≫ g := by
  simpa only [Category.assoc] using congrArg (fun q => k ≫ q) p.2

/-- Precompose both legs of a compatible pullback pair. -/
@[stacks 016U "precomposition of compatible pullback pairs",
  stacks 0173 "precomposition of compatible pullback pairs"]
def precomp {S T : C} (k : S ⟶ T) (p : CompatiblePair f g T) :
    CompatiblePair f g S :=
  ⟨(k ≫ p.1.1, k ≫ p.1.2), precomp_condition f g k p⟩

/-- The first leg of a precomposed compatible pullback pair. -/
@[simp, stacks 016U "first leg after pullback-pair precomposition",
  stacks 0173 "first leg after pullback-pair precomposition"]
theorem precomp_fst {S T : C} (k : S ⟶ T) (p : CompatiblePair f g T) :
    (precomp f g k p).1.1 = k ≫ p.1.1 := rfl

/-- The second leg of a precomposed compatible pullback pair. -/
@[simp, stacks 016U "second leg after pullback-pair precomposition",
  stacks 0173 "second leg after pullback-pair precomposition"]
theorem precomp_snd {S T : C} (k : S ⟶ T) (p : CompatiblePair f g T) :
    (precomp f g k p).1.2 = k ≫ p.1.2 := rfl

/-- The projections of a morphism to a pullback form a compatible pair. -/
@[stacks 016U "pullback projections form a compatible pair",
  stacks 0173 "pullback projections form a compatible pair"]
theorem ofHom_condition {T : C} (h : T ⟶ pullback f g) :
    (h ≫ pullback.fst f g) ≫ f = (h ≫ pullback.snd f g) ≫ g := by
  simpa only [Category.assoc] using
    congrArg (fun q => h ≫ q) (pullback.condition (f := f) (g := g))

/-- Send a morphism to a pullback to its two projection composites. -/
@[stacks 016U "morphism to a compatible pullback pair",
  stacks 0173 "morphism to a compatible pullback pair"]
def ofHom {T : C} (h : T ⟶ pullback f g) : CompatiblePair f g T :=
  ⟨(h ≫ pullback.fst f g, h ≫ pullback.snd f g), ofHom_condition f g h⟩

/-- Construct a morphism to a pullback from a compatible pair. -/
@[stacks 016U "lift of a compatible pullback pair",
  stacks 0173 "lift of a compatible pullback pair"]
noncomputable def lift {T : C} (p : CompatiblePair f g T) : T ⟶ pullback f g :=
  pullback.lift p.1.1 p.1.2 p.2

/-- Lifting the projection pair of a pullback morphism recovers that morphism. -/
@[stacks 016U "pullback lift after projection",
  stacks 0173 "pullback lift after projection"]
theorem lift_ofHom {T : C} (h : T ⟶ pullback f g) :
    lift f g (ofHom f g h) = h := by
  apply pullback.hom_ext
  · show lift f g (ofHom f g h) ≫ pullback.fst f g = h ≫ pullback.fst f g
    simp [lift, ofHom, pullback.lift_fst]
  · show lift f g (ofHom f g h) ≫ pullback.snd f g = h ≫ pullback.snd f g
    simp [lift, ofHom, pullback.lift_snd]

/-- Taking projections after lifting a compatible pullback pair recovers the pair. -/
@[stacks 016U "pullback projections after lift",
  stacks 0173 "pullback projections after lift"]
theorem ofHom_lift {T : C} (p : CompatiblePair f g T) :
    ofHom f g (lift f g p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · change (lift f g p) ≫ pullback.fst f g = p.1.1
    exact pullback.lift_fst _ _ _
  · change (lift f g p) ≫ pullback.snd f g = p.1.2
    exact pullback.lift_snd _ _ _

end CompatiblePair

/-- Morphisms to a pullback are equivalent to compatible pairs of morphisms to its two legs. -/
@[stacks 016U "universal property of pullbacks as a Hom equivalence",
  stacks 0173 "universal property of pullbacks as a Hom equivalence"]
noncomputable def homEquiv (T : C) :
    (T ⟶ pullback f g) ≃ CompatiblePair f g T where
  toFun := CompatiblePair.ofHom f g
  invFun := CompatiblePair.lift f g
  left_inv := CompatiblePair.lift_ofHom f g
  right_inv := CompatiblePair.ofHom_lift f g

namespace homEquiv

/-- The value of `pullback.homEquiv` is the pair of projection composites. -/
@[simp, stacks 016U "pullback Hom equivalence application",
  stacks 0173 "pullback Hom equivalence application"]
theorem apply {T : C} (h : T ⟶ pullback f g) :
    (homEquiv f g T h).1 =
      (h ≫ pullback.fst f g, h ≫ pullback.snd f g) := rfl

/-- The first leg returned by `pullback.homEquiv`. -/
@[simp, stacks 016U "first leg of the pullback Hom equivalence",
  stacks 0173 "first leg of the pullback Hom equivalence"]
theorem apply_fst {T : C} (h : T ⟶ pullback f g) :
    (homEquiv f g T h).1.1 = h ≫ pullback.fst f g := rfl

/-- The second leg returned by `pullback.homEquiv`. -/
@[simp, stacks 016U "second leg of the pullback Hom equivalence",
  stacks 0173 "second leg of the pullback Hom equivalence"]
theorem apply_snd {T : C} (h : T ⟶ pullback f g) :
    (homEquiv f g T h).1.2 = h ≫ pullback.snd f g := rfl

/-- The inverse of `pullback.homEquiv` is the canonical pullback lift. -/
@[simp, stacks 016U "inverse of the pullback Hom equivalence",
  stacks 0173 "inverse of the pullback Hom equivalence"]
theorem symm_apply {T : C} (p : CompatiblePair f g T) :
    (homEquiv f g T).symm p = pullback.lift p.1.1 p.1.2 p.2 := rfl

/-- The pullback Hom equivalence is natural under precomposition. -/
@[simp, stacks 016U "naturality of the pullback Hom equivalence",
  stacks 0173 "naturality of the pullback Hom equivalence"]
theorem precomp {S T : C} (k : S ⟶ T) (h : T ⟶ pullback f g) :
    homEquiv f g S (k ≫ h) =
      CompatiblePair.precomp f g k (homEquiv f g T h) := by
  apply Subtype.ext
  apply Prod.ext
  · change (k ≫ h) ≫ pullback.fst f g = k ≫ (h ≫ pullback.fst f g)
    exact Category.assoc _ _ _
  · change (k ≫ h) ≫ pullback.snd f g = k ≫ (h ≫ pullback.snd f g)
    exact Category.assoc _ _ _

/-- The inverse pullback Hom equivalence commutes with precomposition. -/
@[stacks 016U "inverse naturality of the pullback Hom equivalence",
  stacks 0173 "inverse naturality of the pullback Hom equivalence"]
theorem symm_precomp {S T : C} (k : S ⟶ T) (p : CompatiblePair f g T) :
    (homEquiv f g S).symm (CompatiblePair.precomp f g k p) =
      k ≫ (homEquiv f g T).symm p := by
  apply pullback.hom_ext
  · show (homEquiv f g S).symm (CompatiblePair.precomp f g k p) ≫ pullback.fst f g =
      (k ≫ (homEquiv f g T).symm p) ≫ pullback.fst f g
    simp [Category.assoc, pullback.lift_fst]
  · show (homEquiv f g S).symm (CompatiblePair.precomp f g k p) ≫ pullback.snd f g =
      (k ≫ (homEquiv f g T).symm p) ≫ pullback.snd f g
    simp [Category.assoc, pullback.lift_snd]

end homEquiv

end pullback

end CategoryTheory.Limits
