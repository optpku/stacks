/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernels and Cokernels Under Arrow Isomorphisms

This leaf records the invariant part of kernel and cokernel existence under an
isomorphism in an arrow category. It is independent of additive, biproduct, or
triangulated structure, so later normal-form and localization arguments can
reuse it directly.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Arrow

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Stacks 05QU: an isomorphism of arrows transports existence of a kernel to
the source arrow. -/
@[stacks 05QU]
theorem hasKernel_of_iso {f g : Arrow C} (e : f ≅ g) (hg : HasKernel g.hom) :
    HasKernel f.hom := sorry

/-- Stacks 05QU: an isomorphism of arrows transports existence of a cokernel
to the source arrow. -/
@[stacks 05QU]
theorem hasCokernel_of_iso {f g : Arrow C} (e : f ≅ g) (hg : HasCokernel g.hom) :
    HasCokernel f.hom := sorry

/-- Stacks 05QU: arrow-isomorphism classes preserve the existence of kernels. -/
@[stacks 05QU]
theorem hasKernel_of_isIsomorphic {f g : Arrow C} (e : IsIsomorphic f g)
    (hg : HasKernel g.hom) : HasKernel f.hom := sorry

/-- Stacks 05QU: arrow-isomorphism classes preserve the existence of cokernels. -/
@[stacks 05QU]
theorem hasCokernel_of_isIsomorphic {f g : Arrow C} (e : IsIsomorphic f g)
    (hg : HasCokernel g.hom) : HasCokernel f.hom := sorry

end CategoryTheory.Arrow
