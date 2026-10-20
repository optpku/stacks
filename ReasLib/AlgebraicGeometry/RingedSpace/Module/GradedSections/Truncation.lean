module

public import ReasLib.Algebra.Module.Graded.LowerBound
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections

/-!
# Truncated twisted section modules

This file records lower truncations of integer-graded twisted global sections and the
homogeneous computation rule characterizing the canonical action of the section ring.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.GradedSections

variable {X : RingedSpace.{u}}

/-- The direct sum of twisted global sections in all integer degrees at least `k`. -/
abbrev truncatedTwisted
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) (k : ℤ) : Type _ :=
  ⨁ d, DirectSum.Gmodule.LowerBound.pieces k (twistedDegree L F) d

/-- The lower-truncated twisted section pieces carry the canonical graded-module structure
owned by `DirectSum.Gmodule.LowerBound`. -/
@[stacks 01CV "canonical graded module on lower-truncated twisted sections"]
noncomputable instance instGmoduleTruncatedTwisted
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) (k : ℤ) :
    DirectSum.Gmodule (degree L)
      (DirectSum.Gmodule.LowerBound.pieces k (twistedDegree L F)) :=
  DirectSum.Gmodule.LowerBound.instGmodule (degree L) (twistedDegree L F) k

/-- The action of a homogeneous section on a homogeneous truncated twisted section is the
canonical homogeneous twisted-section action. -/
@[stacks 01CV "homogeneous action on a pure lower-truncated twisted section"]
theorem smul_of
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) (k : ℤ) {m : ℕ}
    (a : degree L m) (d : {d : ℤ // k ≤ d})
    (x : twistedDegree L F d.1) :
    DirectSum.of (degree L) m a •
        DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (twistedDegree L F)) d x =
      DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (twistedDegree L F)) (m +ᵥ d)
        (smul L F a x) := sorry

end AlgebraicGeometry.RingedSpace.GradedSections
