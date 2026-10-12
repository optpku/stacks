/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.Algebra.Module.Submodule.Intersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Intersections and kernels of restricted quotient maps

Let `p` be an `R`-submodule of `M` and let `P` be an `S`-submodule of the same module, where the
`S`-module structure extends the `R`-module structure.  The kernel of `P.mkQ` restricted to `p` is
the intersection of `p` and `P`.  This leaf exposes the kernel equality, a first-class linear
equivalence from the canonical ambient intersection, a source-facing comap bridge, and the
corresponding ambient image equality.

No grading, index type, decidable equality, finiteness, or decomposition is involved.  Graded
quotient components specialize this API by taking `p` to be one homogeneous component.
-/

@[expose] public section

universe u v w

namespace Submodule.Quotient

variable {R : Type u} [Ring R]
variable {S : Type v} [Ring S] [SMul R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

/-- Stacks `00DV`: the kernel of the quotient map restricted to `p` is the intersection with `P`,
presented as a submodule of `p`. -/
@[stacks 00DV "restricted quotient kernel as an intersection"]
theorem ker_eq_comap (p : Submodule R M) (P : Submodule S M) :
    LinearMap.ker ((P.mkQ.restrictScalars R).domRestrict p) =
      (P.restrictScalars R).comap p.subtype := sorry

/-- Stacks `00DV`: the canonical ambient intersection is linearly equivalent to the restricted
quotient kernel inside `p`.

The quotient-independent `toInf` bridge identifies the kernel's native comap presentation with
`p ⊓ P.restrictScalars R`; `ker_eq_comap` is the only quotient-specific equality transport. -/
@[stacks 00DV "ambient intersection-kernel equivalence for a restricted quotient"]
def infEquivKer (p : Submodule R M) (P : Submodule S M) :
    (p ⊓ P.restrictScalars R : Submodule R M) ≃ₗ[R]
      LinearMap.ker ((P.mkQ.restrictScalars R).domRestrict p) :=
  (((Submodule.Intersection.toInf (P.restrictScalars R) p).trans
      (LinearEquiv.ofEq _ _ (inf_comm (P.restrictScalars R) p))).symm).trans
    (LinearEquiv.ofEq _ _ (ker_eq_comap p P).symm)

/-- Stacks `00DV`: the `P`-owned comap presentation of the intersection is linearly equivalent to
the restricted quotient kernel.  This bridge is the specialization used by graded-submodule
callers whose intersection is already packaged inside `P`. -/
@[stacks 00DV "comap intersection-kernel equivalence for a restricted quotient"]
def comapEquivKer (p : Submodule R M) (P : Submodule S M) :
    p.comap (P.restrictScalars R).subtype ≃ₗ[R]
      LinearMap.ker ((P.mkQ.restrictScalars R).domRestrict p) :=
  (Submodule.Intersection.toInf p (P.restrictScalars R)).trans (infEquivKer p P)

/-- Stacks `00DV`: the ambient intersection is the image of the restricted quotient kernel. -/
@[stacks 00DV "restricted quotient kernel as the ambient intersection"]
theorem map_ker_eq_inf (p : Submodule R M) (P : Submodule S M) :
    (LinearMap.ker ((P.mkQ.restrictScalars R).domRestrict p)).map p.subtype =
      p ⊓ P.restrictScalars R := sorry

/-- Stacks `00DV`: the ambient intersection-kernel equivalence preserves the underlying element of
`M`. -/
@[simp, stacks 00DV "restricted quotient ambient intersection-kernel coercion"]
theorem infEquivKer_coe
    (p : Submodule R M) (P : Submodule S M)
    (x : (p ⊓ P.restrictScalars R : Submodule R M)) :
    (infEquivKer p P x : M) = (x : M) := sorry

/-- Stacks `00DV`: the inverse ambient intersection-kernel equivalence preserves the underlying
element of `M`. -/
@[simp, stacks 00DV "restricted quotient kernel-ambient intersection coercion"]
theorem infEquivKer_symm_coe
    (p : Submodule R M) (P : Submodule S M)
    (x : LinearMap.ker ((P.mkQ.restrictScalars R).domRestrict p)) :
    ((infEquivKer p P).symm x : M) = (x : M) := sorry

/-- Stacks `00DV`: the comap intersection-kernel equivalence preserves the underlying element of
`M`. -/
@[simp, stacks 00DV "restricted quotient comap intersection-kernel coercion"]
theorem comapEquivKer_coe
    (p : Submodule R M) (P : Submodule S M)
    (x : p.comap (P.restrictScalars R).subtype) :
    (comapEquivKer p P x : M) = (x : M) := sorry

/-- Stacks `00DV`: the inverse comap intersection-kernel equivalence preserves the underlying
element of `M`. -/
@[simp, stacks 00DV "restricted quotient kernel-comap intersection coercion"]
theorem comapEquivKer_symm_coe
    (p : Submodule R M) (P : Submodule S M)
    (x : LinearMap.ker ((P.mkQ.restrictScalars R).domRestrict p)) :
    ((comapEquivKer p P).symm x : M) = (x : M) := sorry

end Submodule.Quotient
