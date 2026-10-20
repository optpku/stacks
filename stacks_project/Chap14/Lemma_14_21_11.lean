/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Coskeleton.Finiteness
import StacksCheckRecall

/-!
@stack 018V

# Lemma 14.21.11 compatibility facade

The assumption-minimal comparison is owned by
`ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Coskeleton`; its finite-limit and
binary-coproduct integration is the direct leaf imported above. This file retains the historical
Chapter 14 import path and the source label.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable [HasFiniteCoproducts C] [HasFiniteLimits C]
variable (n : ℕ) (V : SimplicialObject C)
variable {M : SimplicialObject C}
variable (R :
  (SimplicialObject.internalHom.presheaf
    ((SSet.sk n).obj (Δ[n + 1] : SSet.{v})) V).RepresentableBy M)

/- Lemma 14.21.11: the degree `n + 1` term of `cosk n V` is canonically isomorphic
to the degree-zero term of any object representing maps from `sk n Δ[n + 1]` to `V`. -/
@[stacks 018V]
#check (SimplicialObject.internalHom.coskeleton.degree.ofRepresentableBy.iso
    (C := C) n (n + 1) V R :
  ((SimplicialObject.cosk n).obj V).obj
      (op (SimplexCategory.mk (n + 1))) ≅
    M.obj (op (SimplexCategory.mk 0)))

/- The forward comparison identifies the two universal elements. -/
#check (SimplicialObject.internalHom.coskeleton.degree.zero.ofRepresentableBy.iso.hom_apply
  (C := C) n (n + 1) V R)

/- The inverse comparison identifies the two universal elements. -/
#check (SimplicialObject.internalHom.coskeleton.degree.zero.ofRepresentableBy.iso.inv_apply
  (C := C) n (n + 1) V R)

end CategoryTheory
