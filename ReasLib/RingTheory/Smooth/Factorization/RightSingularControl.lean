/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.Factorisation
public import ReasLib.RingTheory.Smooth.SingularLocus

@[expose] public section

/-!
# Common finite factorizations with singular-ideal control

This leaf owns the two-source singular-control datum independently of
primewise and principal-power factorization refinements.
-/

universe u v w x

namespace AlgHom.CommonFactorisation.Finite

variable {R : Type u} {A : Type v} {D : Type w} {Λ : Type x}
variable [CommRing R] [CommRing A] [CommRing D] [CommRing Λ]
variable [Algebra R A] [Algebra R D] [Algebra R Λ]

/-- The image of the left source singular ideal in the midpoint of a finite
common factorisation. -/
abbrev leftSingularIdeal {fLeft : A →ₐ[R] Λ} {fRight : D →ₐ[R] Λ}
    (F : AlgHom.CommonFactorisation.Finite fLeft fRight) : Ideal F.mid :=
  Ideal.map F.fromLeft.toRingHom (Algebra.singularIdeal R A)

/-- The image of the right source singular ideal in the midpoint of a finite
common factorisation. -/
abbrev rightSingularIdeal {fLeft : A →ₐ[R] Λ} {fRight : D →ₐ[R] Λ}
    (F : AlgHom.CommonFactorisation.Finite fLeft fRight) : Ideal F.mid :=
  Ideal.map F.fromRight.toRingHom (Algebra.singularIdeal R D)

/-- A finite common factorisation in which the singular ideal of the right
source controls both the relative and absolute singular ideals of the
midpoint. -/
@[stacks 07CT "common finite factorisation with singular control"]
structure RightSingularControl (fLeft : A →ₐ[R] Λ) (fRight : D →ₐ[R] Λ) where
  /-- The underlying finite common factorisation. -/
  base : AlgHom.CommonFactorisation.Finite fLeft fRight
  /-- The source singular ideal maps into the relative singular ideal. -/
  relative_le : base.rightSingularIdeal ≤ AlgHom.singularIdeal base.fromRight
  /-- The source singular ideal maps into the absolute singular ideal. -/
  absolute_le : base.rightSingularIdeal ≤ Algebra.singularIdeal R base.mid

namespace RightSingularControl

variable {fLeft : A →ₐ[R] Λ} {fRight : D →ₐ[R] Λ}

/-- The midpoint of a singular-controlled common factorisation. -/
abbrev mid (F : RightSingularControl fLeft fRight) := F.base.mid

/-- The map from the left source into the controlled midpoint. -/
abbrev fromLeft (F : RightSingularControl fLeft fRight) :
    A →ₐ[R] F.mid := F.base.fromLeft

/-- The map from the right source into the controlled midpoint. -/
abbrev fromRight (F : RightSingularControl fLeft fRight) :
    D →ₐ[R] F.mid := F.base.fromRight

/-- The map from the controlled midpoint to the common target. -/
abbrev toTarget (F : RightSingularControl fLeft fRight) :
    F.mid →ₐ[R] Λ := F.base.toTarget

/-- The left triangle carried by a right-controlled common factorisation. -/
theorem factorLeft (F : RightSingularControl fLeft fRight) :
    F.toTarget.comp F.fromLeft = fLeft := sorry

/-- The right triangle carried by a right-controlled common factorisation. -/
theorem factorRight (F : RightSingularControl fLeft fRight) :
    F.toTarget.comp F.fromRight = fRight := sorry

/-- Attach the two singular-ideal comparisons to a finite common
factorisation. -/
def of (F : AlgHom.CommonFactorisation.Finite fLeft fRight)
    (relative_le : F.rightSingularIdeal ≤ AlgHom.singularIdeal F.fromRight)
    (absolute_le : F.rightSingularIdeal ≤ Algebra.singularIdeal R F.mid) :
    RightSingularControl fLeft fRight :=
  { base := F
    relative_le := relative_le
    absolute_le := absolute_le }

/-- The two singular-ideal comparisons carried by a right-controlled common
factorisation. -/
theorem control (F : RightSingularControl fLeft fRight) :
    F.base.rightSingularIdeal ≤ AlgHom.singularIdeal F.fromRight ∧
      F.base.rightSingularIdeal ≤ Algebra.singularIdeal R F.mid := sorry

/-- The finite-presentation, triangle, and singular-control properties carried
by a controlled common factorisation. -/
theorem spec (F : RightSingularControl fLeft fRight) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromLeft = fLeft ∧
      F.toTarget.comp F.fromRight = fRight ∧
      F.base.rightSingularIdeal ≤ AlgHom.singularIdeal F.fromRight ∧
      F.base.rightSingularIdeal ≤ Algebra.singularIdeal R F.mid := sorry

end RightSingularControl

end AlgHom.CommonFactorisation.Finite
