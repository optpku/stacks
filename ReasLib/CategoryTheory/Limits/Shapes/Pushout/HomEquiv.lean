/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 016X

# Hom equivalences for pushouts

This file packages the universal property of a pushout as an equivalence with compatible pairs of
morphisms. The forward and inverse maps are explicit and remain internal to the ambient category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.Limits.pushout

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) [HasPushout f g]

/-- A compatible pair of morphisms from the two objects under `Z` to `T`. -/
@[stacks 016X "compatible morphism pairs for pushouts"]
abbrev CompatiblePair (T : C) :=
  { p : (X ⟶ T) × (Y ⟶ T) // f ≫ p.1 = g ≫ p.2 }

namespace CompatiblePair

/-- Postcomposition preserves the compatibility equation for a pushout pair. -/
@[stacks 016X "postcomposition of compatible pushout pairs"]
theorem postcomp_condition {S T : C} (p : CompatiblePair f g S) (k : S ⟶ T) :
    f ≫ (p.1.1 ≫ k) = g ≫ (p.1.2 ≫ k) := by
  simpa only [Category.assoc] using congrArg (fun h : Z ⟶ S => h ≫ k) p.2

/-- Postcompose both legs of a compatible pushout pair. -/
@[stacks 016X "postcomposition of compatible pushout pairs"]
def postcomp {S T : C} (p : CompatiblePair f g S) (k : S ⟶ T) :
    CompatiblePair f g T :=
  ⟨(p.1.1 ≫ k, p.1.2 ≫ k), postcomp_condition f g p k⟩

/-- The first leg of a postcomposed compatible pushout pair. -/
@[simp, stacks 016X "first leg after pushout-pair postcomposition"]
theorem postcomp_fst {S T : C} (p : CompatiblePair f g S) (k : S ⟶ T) :
    (postcomp f g p k).1.1 = p.1.1 ≫ k := rfl

/-- The second leg of a postcomposed compatible pushout pair. -/
@[simp, stacks 016X "second leg after pushout-pair postcomposition"]
theorem postcomp_snd {S T : C} (p : CompatiblePair f g S) (k : S ⟶ T) :
    (postcomp f g p k).1.2 = p.1.2 ≫ k := rfl

/-- The inclusion composites of a morphism from a pushout form a compatible pair. -/
@[stacks 016X "pushout inclusions form a compatible pair"]
theorem ofHom_condition {T : C} (h : pushout f g ⟶ T) :
    f ≫ (pushout.inl f g ≫ h) = g ≫ (pushout.inr f g ≫ h) := by
  simpa only [Category.assoc] using
    congrArg (fun k : Z ⟶ pushout f g => k ≫ h) (pushout.condition (f := f) (g := g))

/-- Send a morphism from a pushout to its two inclusion composites. -/
@[stacks 016X "morphism from a compatible pushout pair"]
def ofHom {T : C} (h : pushout f g ⟶ T) : CompatiblePair f g T :=
  ⟨(pushout.inl f g ≫ h, pushout.inr f g ≫ h), ofHom_condition f g h⟩

/-- Construct a morphism from a pushout from a compatible pair. -/
@[stacks 016X "descent of a compatible pushout pair"]
noncomputable def desc {T : C} (p : CompatiblePair f g T) : pushout f g ⟶ T :=
  pushout.desc p.1.1 p.1.2 p.2

/-- Descending the inclusion pair of a pushout morphism recovers that morphism. -/
@[stacks 016X "pushout descent after inclusions"]
theorem desc_ofHom {T : C} (h : pushout f g ⟶ T) :
    desc f g (ofHom f g h) = h := by
  apply pushout.hom_ext
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

/-- Taking inclusion composites after descending a compatible pushout pair recovers the pair. -/
@[stacks 016X "pushout inclusions after descent"]
theorem ofHom_desc {T : C} (p : CompatiblePair f g T) :
    ofHom f g (desc f g p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

end CompatiblePair

/-- Morphisms from a pushout are equivalent to compatible pairs from its two legs. -/
@[stacks 016X "universal property of pushouts as a Hom equivalence"]
noncomputable def homEquiv (T : C) :
    (pushout f g ⟶ T) ≃ CompatiblePair f g T where
  toFun := CompatiblePair.ofHom f g
  invFun := CompatiblePair.desc f g
  left_inv := CompatiblePair.desc_ofHom f g
  right_inv := CompatiblePair.ofHom_desc f g

namespace homEquiv

/-- The value of `pushout.homEquiv` is the pair of inclusion composites. -/
@[simp, stacks 016X "pushout Hom equivalence application"]
theorem apply {T : C} (h : pushout f g ⟶ T) :
    (homEquiv f g T h).1 =
      (pushout.inl f g ≫ h, pushout.inr f g ≫ h) := rfl

/-- The first leg returned by `pushout.homEquiv`. -/
@[simp, stacks 016X "first leg of the pushout Hom equivalence"]
theorem apply_inl {T : C} (h : pushout f g ⟶ T) :
    (homEquiv f g T h).1.1 = pushout.inl f g ≫ h := rfl

/-- The second leg returned by `pushout.homEquiv`. -/
@[simp, stacks 016X "second leg of the pushout Hom equivalence"]
theorem apply_inr {T : C} (h : pushout f g ⟶ T) :
    (homEquiv f g T h).1.2 = pushout.inr f g ≫ h := rfl

/-- The inverse of `pushout.homEquiv` is the canonical pushout descent. -/
@[simp, stacks 016X "inverse of the pushout Hom equivalence"]
theorem symm_apply {T : C} (p : CompatiblePair f g T) :
    (homEquiv f g T).symm p = pushout.desc p.1.1 p.1.2 p.2 := rfl

/-- The pushout Hom equivalence is natural under postcomposition. -/
@[simp, stacks 016X "naturality of the pushout Hom equivalence"]
theorem postcomp {S T : C} (h : pushout f g ⟶ S) (k : S ⟶ T) :
    homEquiv f g T (h ≫ k) =
      CompatiblePair.postcomp f g (homEquiv f g S h) k := by
  apply Subtype.ext
  apply Prod.ext
  · exact (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).symm

/-- The inverse pushout Hom equivalence commutes with postcomposition. -/
@[stacks 016X "inverse naturality of the pushout Hom equivalence"]
theorem symm_postcomp {S T : C} (p : CompatiblePair f g S) (k : S ⟶ T) :
    (homEquiv f g T).symm (CompatiblePair.postcomp f g p k) =
      (homEquiv f g S).symm p ≫ k := by
  apply (homEquiv f g T).injective
  rw [(homEquiv f g T).apply_symm_apply, postcomp, (homEquiv f g S).apply_symm_apply]

end homEquiv

end CategoryTheory.Limits.pushout
