/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.FiniteType.Transport
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Neutral degree-zero support for graded algebras

This leaf contains only constructions attached to the degree-zero component of an internally
graded algebra.  In particular, it does not mention localization: localization-specific bridges
belong in the homogeneous-localization leaves.
-/

@[expose] public section

noncomputable section

universe u v w

namespace SetLike.GradeZero

variable {ι : Type u} [AddMonoid ι] [DecidableEq ι]
variable {R : Type v} {S : Type w}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]

/-- The external base ring, the degree-zero piece, and the ambient graded algebra form a scalar
tower.  The instance is neutral and therefore available independently of any localization. -/
@[stacks 00JR "degree-zero scalar tower"]
instance instIsScalarTower : IsScalarTower R (𝒜 0) S := sorry

end SetLike.GradeZero

namespace GradedAlgebra

variable {ι : Type u} [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι]
  [CanonicallyOrderedAdd ι]
variable {R : Type v} {S : Type w}
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]

/-- The canonical `R`-algebra homomorphism projecting a graded algebra to its degree-zero
component.  Its underlying ring homomorphism is Mathlib's `GradedRing.projZeroRingHom'`. -/
@[stacks 00JR "degree-zero algebra projection"]
def projZeroAlgHom : S →ₐ[R] 𝒜 0 where
  toRingHom := GradedRing.projZeroRingHom' 𝒜
  commutes' := sorry

/-- The underlying value of the degree-zero algebra projection is the canonical graded-ring
projection. -/
@[simp, stacks 00JR "degree-zero projection value"]
theorem projZeroAlgHom_apply (a : S) :
    (projZeroAlgHom 𝒜 a : S) = GradedRing.projZeroRingHom 𝒜 a := sorry

/-- The degree-zero projection restricts to the identity on the degree-zero component. -/
@[simp, stacks 00JR "degree-zero projection identity"]
theorem projZeroAlgHom_apply_coe (a : 𝒜 0) :
    projZeroAlgHom 𝒜 (a : S) = a := sorry

/-- The degree-zero algebra projection is surjective. -/
@[stacks 00JR "degree-zero projection surjectivity"]
theorem projZeroAlgHom_surjective :
    Function.Surjective (projZeroAlgHom 𝒜) := sorry

/-- Finite type of the ambient graded algebra descends to its degree-zero component. -/
@[stacks 07Z2 "finite type of the degree-zero component"]
theorem finiteType_degreeZero [Algebra.FiniteType R S] :
    Algebra.FiniteType R (𝒜 0) := sorry

end GradedAlgebra

namespace GradedAlgebra

variable {ι : Type u} [AddMonoid ι] [DecidableEq ι]
variable {R : Type v} {S : Type w}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]

/-- Finite type of the ambient graded algebra can also be viewed over its degree-zero component.
This is the canonical bridge used by localization results whose coefficient ring is `𝒜 0`. -/
@[stacks 07Z2 "finite type over the degree-zero component"]
theorem finiteType_over_degreeZero [Algebra.FiniteType R S] :
    Algebra.FiniteType (𝒜 0) S := sorry

end GradedAlgebra

namespace GradedAlgebra

variable {ι : Type w} [AddMonoid ι] [DecidableEq ι]
variable {R : Type u} {S : Type v}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (𝒜 : ι → Submodule R S) [GradedAlgebra 𝒜]

/-- Finite type over the degree-zero piece descends along an algebra equivalence with the base.

This specialization keeps the common graded-algebra notation for an arbitrary additively graded
index while delegating the base-change principle to
`Algebra.FiniteType.of_algEquiv`. -/
@[stacks 00P6 "finite type from an equivalent degree-zero base"]
theorem finiteType_of_degreeZeroEquiv [Algebra.FiniteType (𝒜 0) S]
    (zeroEquiv : R ≃ₐ[R] 𝒜 0) :
    Algebra.FiniteType R S := sorry

end GradedAlgebra
