/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative finite presentation of modules

An `A`-module is finitely presented relative to `R` when it is finitely presented over one
finite-variable polynomial presentation of the ambient finite type `R`-algebra `A`.
-/

universe u v w

namespace Module

universe u' v' w'

/-- Finite presentation of a module after restricting scalars along an explicit ring homomorphism.
This predicate fixes the scalar action without installing it as a local instance. -/
@[stacks 05GZ "finite presentation along a ring homomorphism"]
def FinitePresentationAlong
    {R : Type u'} {A : Type v'} [Semiring R] [Semiring A]
    (f : R →+* A) (M : Type w') [AddCommMonoid M] [Module A M] : Prop :=
  @Module.FinitePresentation R M _ _ (Module.compHom M f)

variable (R : Type u) (A : Type v) (M : Type w)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

/-- An `A`-module is finitely presented relative to `R` when it is finitely
presented over one finite-variable polynomial presentation of `A` over `R`. -/
@[stacks 05GZ "relative finite presentation of a module"]
def FinitePresentationRelativeTo : Prop :=
  ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
    Function.Surjective α ∧ Module.FinitePresentationAlong α.toRingHom M

namespace FinitePresentationRelativeTo

/-- Relative finite presentation forces the ambient algebra to be of finite type. -/
@[stacks 05GZ "relative finite presentation forces finite type"]
theorem finiteType (hM : FinitePresentationRelativeTo R A M) :
    Algebra.FiniteType R A := sorry
/- Proof strategy: unpack the polynomial-presentation witness in `hM`; the finite-variable
`MvPolynomial` algebra is finite type, and `Algebra.FiniteType.of_surjective` descends finite type
along the witness map. -/

/-- A relatively finitely presented module is finitely presented over its ambient algebra. -/
@[stacks 05GZ "relative finite presentation implies module finite presentation"]
theorem finitePresentation (hM : FinitePresentationRelativeTo R A M) :
    Module.FinitePresentation A M := sorry
/- Proof strategy: unpack the witness `α : MvPolynomial (Fin n) R →ₐ[R] A`, view its
`FinitePresentationAlong` field as finite presentation after restriction to the polynomial ring,
and apply `Module.FinitePresentation.of_restrictScalars` using finite type of the surjective map
`α`. -/

end FinitePresentationRelativeTo

end Module
