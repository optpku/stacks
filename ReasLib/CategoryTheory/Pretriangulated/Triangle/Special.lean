/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Special and Co-special Triangles

This leaf separates the Hom-exactness properties of an arbitrary triangle from
the stronger hypothesis that it is distinguished.  The covariant property is
primitive; the contravariant property is its canonical opposite-category view.
This makes both properties available in settings where a chosen class of
triangles is not yet installed as a pretriangulated structure.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe v u

namespace CategoryTheory.Pretriangulated.Triangle

open CategoryTheory.Pretriangulated.Opposite

variable {D : Type u} [Category.{v} D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

/-- Remark 13.4.4 (1), Stacks 09WA: a triangle is special when every shift has
exact covariant Hom sequences in all three adjacent positions. -/
@[stacks 09WA]
class IsSpecial (T : Triangle D) : Prop where
  /-- Exactness at the second object of each shifted special triangle. -/
  exact₂ (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₁))
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₂))
  /-- Exactness at the third object of each shifted special triangle. -/
  exact₃ (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₂))
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₃))
  /-- Exactness at the shifted first object of each shifted special triangle. -/
  exact₁ (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₃))
      ((preadditiveCoyoneda.obj (op W)).map (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧'))

namespace IsSpecial

variable {T : Triangle D}

/-- The unshifted first covariant exact pair of a special triangle. -/
theorem exact₂_unshifted (hT : IsSpecial T) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T.mor₁)
      ((preadditiveCoyoneda.obj (op W)).map T.mor₂) := sorry

/-- The unshifted second covariant exact pair of a special triangle. -/
theorem exact₃_unshifted (hT : IsSpecial T) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T.mor₂)
      ((preadditiveCoyoneda.obj (op W)).map T.mor₃) := sorry

/-- The unshifted third covariant exact pair of a special triangle. -/
theorem exact₁_unshifted (hT : IsSpecial T) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T.mor₃)
      ((preadditiveCoyoneda.obj (op W)).map (T.mor₁⟦(1 : ℤ)⟧')) := sorry

/-- Stacks 09WA: covariant Hom exactness at the second object, expressed as a
factorization through the first morphism. -/
@[stacks 09WA]
theorem coyoneda_exact₂ (hT : IsSpecial T) (n : ℤ) (W : D)
    {f : W ⟶ (T⟦n⟧ : Triangle D).obj₂}
    (hf : f ≫ (T⟦n⟧ : Triangle D).mor₂ = 0) :
    ∃ g : W ⟶ (T⟦n⟧ : Triangle D).obj₁,
      f = g ≫ (T⟦n⟧ : Triangle D).mor₁ := sorry

/-- Stacks 09WA: covariant Hom exactness at the third object, expressed as a
factorization through the second morphism. -/
@[stacks 09WA]
theorem coyoneda_exact₃ (hT : IsSpecial T) (n : ℤ) (W : D)
    {f : W ⟶ (T⟦n⟧ : Triangle D).obj₃}
    (hf : f ≫ (T⟦n⟧ : Triangle D).mor₃ = 0) :
    ∃ g : W ⟶ (T⟦n⟧ : Triangle D).obj₂,
      f = g ≫ (T⟦n⟧ : Triangle D).mor₂ := sorry

/-- Stacks 09WA: covariant Hom exactness at the shifted first object,
expressed as a factorization through the third morphism. -/
@[stacks 09WA]
theorem coyoneda_exact₁ (hT : IsSpecial T) (n : ℤ) (W : D)
    {f : W ⟶ (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧}
    (hf : f ≫ (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') = 0) :
    ∃ g : W ⟶ (T⟦n⟧ : Triangle D).obj₃,
      f = g ≫ (T⟦n⟧ : Triangle D).mor₃ := sorry

/-- The unshifted first covariant exactness factorization. -/
theorem coyoneda_exact₂_unshifted (hT : IsSpecial T) (W : D)
    {f : W ⟶ T.obj₂} (hf : f ≫ T.mor₂ = 0) :
    ∃ g : W ⟶ T.obj₁, f = g ≫ T.mor₁ := sorry

/-- The unshifted second covariant exactness factorization. -/
theorem coyoneda_exact₃_unshifted (hT : IsSpecial T) (W : D)
    {f : W ⟶ T.obj₃} (hf : f ≫ T.mor₃ = 0) :
    ∃ g : W ⟶ T.obj₂, f = g ≫ T.mor₂ := sorry

/-- The unshifted third covariant exactness factorization. -/
theorem coyoneda_exact₁_unshifted (hT : IsSpecial T) (W : D)
    {f : W ⟶ T.obj₁⟦(1 : ℤ)⟧} (hf : f ≫ (T.mor₁⟦(1 : ℤ)⟧') = 0) :
    ∃ g : W ⟶ T.obj₃, f = g ≫ T.mor₃ := sorry

/-- The first two morphisms of every shifted special triangle compose to zero. -/
theorem zero₁₂ (hT : IsSpecial T) (n : ℤ) :
    (T⟦n⟧ : Triangle D).mor₁ ≫ (T⟦n⟧ : Triangle D).mor₂ = 0 := sorry

/-- The second and third morphisms of every shifted special triangle compose to zero. -/
theorem zero₂₃ (hT : IsSpecial T) (n : ℤ) :
    (T⟦n⟧ : Triangle D).mor₂ ≫ (T⟦n⟧ : Triangle D).mor₃ = 0 := sorry

/-- The third and shifted first morphisms of every shifted special triangle
compose to zero. -/
theorem zero₃₁ (hT : IsSpecial T) (n : ℤ) :
    (T⟦n⟧ : Triangle D).mor₃ ≫ (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') = 0 := sorry

/-- The first two morphisms of a special triangle compose to zero. -/
theorem zero₁₂_unshifted (hT : IsSpecial T) : T.mor₁ ≫ T.mor₂ = 0 := sorry

/-- The second and third morphisms of a special triangle compose to zero. -/
theorem zero₂₃_unshifted (hT : IsSpecial T) : T.mor₂ ≫ T.mor₃ = 0 := sorry

/-- Specialness transports across an isomorphism of triangles. -/
@[stacks 09WA]
theorem ofIso {T' : Triangle D} (e : T ≅ T') (hT : IsSpecial T) :
    IsSpecial T' := sorry

/-- Specialness is stable under an arbitrary triangle shift. -/
@[stacks 09WA]
theorem shift (hT : IsSpecial T) (n : ℤ) :
    IsSpecial (T⟦n⟧ : Triangle D) := sorry

/-- Triangle shifts preserve specialness through typeclass search. -/
instance instShift (n : ℤ) [IsSpecial T] :
    IsSpecial (T⟦n⟧ : Triangle D) := sorry

/-- Specialness is stable under rotation. -/
@[stacks 09WA]
theorem rotate (hT : IsSpecial T) : IsSpecial T.rotate := sorry

/-- Triangle rotation preserves specialness through typeclass search. -/
instance instRotate [IsSpecial T] : IsSpecial T.rotate := sorry

/-- Specialness is stable under inverse rotation. -/
@[stacks 09WA]
theorem invRotate (hT : IsSpecial T) : IsSpecial T.invRotate := sorry

/-- Inverse triangle rotation preserves specialness through typeclass search. -/
instance instInvRotate [IsSpecial T] : IsSpecial T.invRotate := sorry

end IsSpecial

/-- Remark 13.4.4 (2), Stacks 09WA: a triangle is co-special when its canonical
opposite-category triangle is special. This is the natural contravariant
Hom-exactness view. -/
@[stacks 09WA]
noncomputable abbrev IsCoSpecial (T : Triangle D) : Prop :=
  IsSpecial ((triangleOpEquivalence D).functor.obj (op T))

namespace IsCoSpecial

variable {T : Triangle D}

/-- Co-specialness transports across an isomorphism of triangles. -/
@[stacks 09WA]
theorem ofIso {T' : Triangle D} (e : T ≅ T') (hT : IsCoSpecial T) :
    IsCoSpecial T' := sorry

/-- Co-specialness is stable under an arbitrary triangle shift. -/
@[stacks 09WA]
theorem shift (hT : IsCoSpecial T) (n : ℤ) :
    IsCoSpecial (T⟦n⟧ : Triangle D) := sorry

/-- Triangle shifts preserve co-specialness through typeclass search. -/
instance instShift (n : ℤ) [IsCoSpecial T] :
    IsCoSpecial (T⟦n⟧ : Triangle D) := sorry

/-- Co-specialness is stable under rotation. -/
@[stacks 09WA]
theorem rotate (hT : IsCoSpecial T) : IsCoSpecial T.rotate := sorry

/-- Triangle rotation preserves co-specialness through typeclass search. -/
instance instRotate [IsCoSpecial T] : IsCoSpecial T.rotate := sorry

/-- Co-specialness is stable under inverse rotation. -/
@[stacks 09WA]
theorem invRotate (hT : IsCoSpecial T) : IsCoSpecial T.invRotate := sorry

/-- Inverse triangle rotation preserves co-specialness through typeclass search. -/
instance instInvRotate [IsCoSpecial T] : IsCoSpecial T.invRotate := sorry

/-- The unshifted first contravariant exactness factorization. -/
theorem yoneda_exact₂_unshifted (hT : IsCoSpecial T) (W : D)
    {f : T.obj₂ ⟶ W} (hf : T.mor₁ ≫ f = 0) :
    ∃ g : T.obj₃ ⟶ W, f = T.mor₂ ≫ g := sorry

/-- The unshifted second contravariant exactness factorization. -/
theorem yoneda_exact₃_unshifted (hT : IsCoSpecial T) (W : D)
    {f : T.obj₃ ⟶ W} (hf : T.mor₂ ≫ f = 0) :
    ∃ g : T.obj₁⟦(1 : ℤ)⟧ ⟶ W, f = T.mor₃ ≫ g := sorry

/-- The unshifted third contravariant exactness factorization. -/
theorem yoneda_exact₁_unshifted (hT : IsCoSpecial T) (W : D)
    {f : T.obj₁⟦(1 : ℤ)⟧ ⟶ W} (hf : T.mor₃ ≫ f = 0) :
    ∃ g : T.obj₂⟦(1 : ℤ)⟧ ⟶ W, f = (T.mor₁⟦(1 : ℤ)⟧') ≫ g := sorry

/-- Stacks 09WA: contravariant Hom exactness at the second object. -/
@[stacks 09WA]
theorem yoneda_exact₂ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₂ ⟶ W}
    (hf : (T⟦n⟧ : Triangle D).mor₁ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₃ ⟶ W,
      f = (T⟦n⟧ : Triangle D).mor₂ ≫ g := sorry

/-- Stacks 09WA: contravariant Hom exactness at the third object. -/
@[stacks 09WA]
theorem yoneda_exact₃ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₃ ⟶ W}
    (hf : (T⟦n⟧ : Triangle D).mor₂ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧ ⟶ W,
      f = (T⟦n⟧ : Triangle D).mor₃ ≫ g := sorry

/-- Stacks 09WA: contravariant Hom exactness at the shifted first object. -/
@[stacks 09WA]
theorem yoneda_exact₁ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧ ⟶ W}
    (hf : (T⟦n⟧ : Triangle D).mor₃ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₂⟦(1 : ℤ)⟧ ⟶ W,
      f = (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') ≫ g := sorry

/-- The first two morphisms of every shifted co-special triangle compose to zero. -/
theorem zero₁₂ (hT : IsCoSpecial T) (n : ℤ) :
    (T⟦n⟧ : Triangle D).mor₁ ≫ (T⟦n⟧ : Triangle D).mor₂ = 0 := sorry

/-- The second and third morphisms of every shifted co-special triangle compose to zero. -/
theorem zero₂₃ (hT : IsCoSpecial T) (n : ℤ) :
    (T⟦n⟧ : Triangle D).mor₂ ≫ (T⟦n⟧ : Triangle D).mor₃ = 0 := sorry

/-- The third and shifted first morphisms of every shifted co-special triangle
compose to zero. -/
theorem zero₃₁ (hT : IsCoSpecial T) (n : ℤ) :
    (T⟦n⟧ : Triangle D).mor₃ ≫ (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') = 0 := sorry

end IsCoSpecial

section Distinguished

variable [HasZeroObject D] [Pretriangulated D]

/-- Remark 13.4.4 (9), Stacks 09WA: every distinguished triangle is special.
This is an explicit bridge theorem rather than a noncanonical instance carrying
a proof argument. -/
@[stacks 09WA]
theorem isSpecial_of_distinguished (T : Triangle D) (hT : T ∈ distTriang D) :
    IsSpecial T := sorry

/-- Remark 13.4.4 (10), Stacks 09WA: every distinguished triangle is
co-special. This is the opposite-category companion of
`isSpecial_of_distinguished`. -/
@[stacks 09WA]
theorem isCoSpecial_of_distinguished (T : Triangle D) (hT : T ∈ distTriang D) :
    IsCoSpecial T := sorry

end Distinguished

/-- Remark 13.4.4 (3), Stacks 09WA: a morphism of special triangles whose outer
components are isomorphisms has an isomorphic middle component. -/
@[stacks 09WA]
theorem isIso₂_of_isIso₁₃_of_isSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : IsSpecial T) (hT' : IsSpecial T') (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₂ := sorry

/-- Remark 13.4.4 (4), Stacks 09WA: a morphism of special triangles whose first
two components are isomorphisms has an isomorphic third component. -/
@[stacks 09WA]
theorem isIso₃_of_isIso₁₂_of_isSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : IsSpecial T) (hT' : IsSpecial T') (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) :
    IsIso φ.hom₃ := sorry

/-- Remark 13.4.4 (5), Stacks 09WA: a morphism of special triangles whose last
two components are isomorphisms has an isomorphic first component. -/
@[stacks 09WA]
theorem isIso₁_of_isIso₂₃_of_isSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : IsSpecial T) (hT' : IsSpecial T') (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₁ := sorry

/-- Remark 13.4.4 (6), Stacks 09WA: a morphism of co-special triangles whose
outer components are isomorphisms has an isomorphic middle component. -/
@[stacks 09WA]
theorem isIso₂_of_isIso₁₃_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : IsCoSpecial T) (hT' : IsCoSpecial T') (h₁ : IsIso φ.hom₁) (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₂ := sorry

/-- Remark 13.4.4 (7), Stacks 09WA: a morphism of co-special triangles whose
first two components are isomorphisms has an isomorphic third component. -/
@[stacks 09WA]
theorem isIso₃_of_isIso₁₂_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : IsCoSpecial T) (hT' : IsCoSpecial T') (h₁ : IsIso φ.hom₁) (h₂ : IsIso φ.hom₂) :
    IsIso φ.hom₃ := sorry

/-- Remark 13.4.4 (8), Stacks 09WA: a morphism of co-special triangles whose
last two components are isomorphisms has an isomorphic first component. -/
@[stacks 09WA]
theorem isIso₁_of_isIso₂₃_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : IsCoSpecial T) (hT' : IsCoSpecial T') (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₁ := sorry

end CategoryTheory.Pretriangulated.Triangle
