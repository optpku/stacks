/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Quotient
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.SquareZero

@[expose] public section

/-!
# Quotients of square-zero dual-number modules

This file compares reduction modulo `ε` for a module built from a square-zero endomorphism with
the cokernel of that endomorphism. It is separated from the basic square-zero construction so
consumers of the action and reconstruction API do not import quotient infrastructure.
-/

universe u v

open scoped DualNumber

namespace ModuleCat.DualNumber

variable {R : Type u} [CommRing R]
variable {X : Type v} [AddCommGroup X] [Module R X]

namespace OfSquareZero

/-- On `ofSquareZero e he`, the submodule `εM` has the same underlying set as
`LinearMap.range e`. -/
@[simp]
theorem mem_epsSubmodule_iff (e : Module.End R X) (he : e.comp e = 0) (x : X) :
    x ∈ epsSubmodule (ofSquareZero e he) ↔ x ∈ LinearMap.range e := by
  constructor
  · rintro ⟨y, hy⟩
    have happly : (show X from (epsEnd (ofSquareZero e he)).hom y) = e y :=
      epsEnd_apply_ofSquareZero e he y
    have hy' : (show X from (epsEnd (ofSquareZero e he)).hom y) = x := hy
    exact ⟨y, happly.symm.trans hy'⟩
  · rintro ⟨y, hy⟩
    have happly : (show X from (epsEnd (ofSquareZero e he)).hom y) = e y :=
      epsEnd_apply_ofSquareZero e he y
    exact ⟨y, happly.trans hy⟩

/-- Transporting the restricted epsilon submodule along the canonical restriction equivalence
gives the range of the square-zero endomorphism. -/
@[stacks 05CS "transported square-zero epsilon submodule"]
theorem map_restrictedEpsSubmodule (e : Module.End R X) (he : e.comp e = 0) :
    (restrictedEpsSubmodule (ofSquareZero e he)).map
      (restrictEquiv e he).toLinearMap = LinearMap.range e := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [restrictEquiv] using
      (mem_epsSubmodule_iff e he y).mp
        ((mem_restrictedEpsSubmodule_iff (ofSquareZero e he) y).mp hy)
  · intro hx
    refine ⟨x, ?_, rfl⟩
    exact (mem_restrictedEpsSubmodule_iff (ofSquareZero e he) x).mpr
      ((mem_epsSubmodule_iff e he x).mpr hx)

/-- Quotienting `ofSquareZero e he` by `εM` recovers the cokernel of `e` over `R`. -/
@[stacks 05CS "square-zero epsilon quotient"]
noncomputable def epsQuotientEquiv (e : Module.End R X) (he : e.comp e = 0) :
    epsQuotient (ofSquareZero e he) ≃ₗ[R] (X ⧸ LinearMap.range e) :=
  Submodule.Quotient.equiv
    (restrictedEpsSubmodule (ofSquareZero e he)) (LinearMap.range e)
    (restrictEquiv e he) (map_restrictedEpsSubmodule e he)

/-- The square-zero quotient equivalence preserves quotient representatives. -/
@[simp]
theorem epsQuotientEquiv_mk (e : Module.End R X) (he : e.comp e = 0) (x : X) :
    epsQuotientEquiv e he (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  change Submodule.Quotient.mk (restrictEquiv e he x) = Submodule.Quotient.mk x
  rfl

/-- The inverse square-zero quotient equivalence preserves quotient representatives. -/
@[simp]
theorem epsQuotientEquiv_symm_mk (e : Module.End R X) (he : e.comp e = 0) (x : X) :
    (epsQuotientEquiv e he).symm (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : epsQuotient (ofSquareZero e he)) := by
  apply (epsQuotientEquiv e he).injective
  simp

end OfSquareZero

end ModuleCat.DualNumber
