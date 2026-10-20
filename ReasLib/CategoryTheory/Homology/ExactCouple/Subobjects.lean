/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple
public import ReasLib.CategoryTheory.Subobject.Image
public import ReasLib.CategoryTheory.Subobject.Kernel
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Kernel and Image Formulas for Exact Couples

This module exposes the subobject identities that identify the cycles and boundaries of the first
derived page. The generic kernel-of-composite and image-of-composite calculations remain owned by
the corresponding `Subobject` modules.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (X : ExactCouple C)

/-- Exactness at the target of `α` identifies `image α` with `kernel g`. -/
@[stacks 011R "outer image-kernel identification"]
theorem Image.alpha_eq_kernel_g :
    imageSubobject X.α = kernelSubobject X.g := sorry

/-- Exactness at the page object identifies `image g` with `kernel f`. -/
@[stacks 011R "page image-kernel identification"]
theorem Image.g_eq_kernel_f :
    imageSubobject X.g = kernelSubobject X.f := sorry

/-- Exactness at the source of `α` identifies `image f` with `kernel α`. -/
@[stacks 011R "source image-kernel identification"]
theorem Image.f_eq_kernel_alpha :
    imageSubobject X.f = kernelSubobject X.α := sorry

/-- The kernel of the page differential is the pullback of `kernel g` along `f`. -/
@[stacks 011R "page-differential kernel formula"]
theorem Kernel.d_eq_pullback_g :
    kernelSubobject X.d = (Subobject.pullback X.f).obj (kernelSubobject X.g) := sorry

/-- 011R (Lemma 12.21.2) (1): `kernel d` is the inverse image of `image α` under `f`. -/
@[stacks 011R "page-differential cycle formula"]
theorem Kernel.d_eq_preimage_image_alpha :
    kernelSubobject X.d = (Subobject.pullback X.f).obj (imageSubobject X.α) := sorry

/-- The image of the page differential is the image of `g` restricted to `image f`. -/
@[stacks 011R "page-differential image formula"]
theorem Image.d_eq_g_on_image_f :
    imageSubobject X.d = imageSubobject ((imageSubobject X.f).arrow ≫ X.g) := sorry

/-- 011R (Lemma 12.21.2) (2): `image d` is the image under `g` of `kernel α`. -/
@[stacks 011R "page-differential boundary formula"]
theorem Image.d_eq_g_on_kernel_alpha :
    imageSubobject X.d = imageSubobject ((kernelSubobject X.α).arrow ≫ X.g) := sorry

end ExactCouple
end CategoryTheory
