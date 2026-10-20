/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Intersections and their subtype presentations

For two submodules `p q : Submodule R M`, the canonical carrier is the lattice intersection
`p ⊓ q`.  Mathlib also exposes two subtype presentations, `p.comap q.subtype` and
`q.comap p.subtype`; this leaf provides one orientation bridge to `p ⊓ q` and derives the carrier
swap by symmetry.  No quotient, grading, or finiteness assumption belongs here.
-/

@[expose] public section

universe u v

namespace Submodule.Intersection

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Stacks `052N`: identify the `q`-owned subtype presentation with the ambient intersection. -/
@[stacks 052N "intersection subtype to ambient infimum"]
def toInf (p q : Submodule R M) :
    p.comap q.subtype ≃ₗ[R] (p ⊓ q : Submodule R M) :=
  (q.equivSubtypeMap (p.comap q.subtype)).trans
    (LinearEquiv.ofEq _ _ ((Submodule.map_comap_subtype q p).trans (inf_comm q p)))

/-- Stacks `052N`: swap the two native subtype presentations of an intersection. -/
@[stacks 052N "intersection subtype swap equivalence"]
def swapEquiv (p q : Submodule R M) :
    p.comap q.subtype ≃ₗ[R] q.comap p.subtype :=
  (toInf p q).trans
    ((LinearEquiv.ofEq _ _ (inf_comm p q)).trans (toInf q p).symm)

/-- Stacks `052N`: the ambient value of `toInf` is unchanged. -/
@[simp, stacks 052N "intersection subtype ambient computation"]
theorem toInf_coe (p q : Submodule R M) (x : p.comap q.subtype) :
    (toInf p q x : M) = (x : M) := sorry

/-- Stacks `052N`: the inverse of `toInf` also preserves the represented ambient element. -/
@[simp, stacks 052N "inverse intersection subtype ambient computation"]
theorem toInf_symm_coe (p q : Submodule R M) (x : (p ⊓ q : Submodule R M)) :
    ((toInf p q).symm x : M) = (x : M) := sorry

/-- Stacks `052N`: the subtype swap preserves the ambient element. -/
@[simp, stacks 052N "intersection subtype swap computation"]
theorem swapEquiv_coe (p q : Submodule R M) (x : p.comap q.subtype) :
    (swapEquiv p q x : M) = (x : M) := sorry

/-- Stacks `052N`: swapping the two submodules gives the inverse equivalence. -/
@[simp, stacks 052N "symmetry of the intersection subtype swap"]
theorem swapEquiv_symm (p q : Submodule R M) :
    (swapEquiv p q).symm = swapEquiv q p := sorry

end Submodule.Intersection
