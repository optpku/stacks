/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.OverField.Equidimensional
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.KrullDimension.Relative

@[expose] public section

/-!
# Relative Dimension of Global Complete Intersections

This module relates the local dimensions of residue-field fibers of a relative
global complete-intersection presentation to its presentation dimension.
-/

universe u v

namespace Algebra

namespace Presentation

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n c : ℕ}

namespace IsRelativeGlobalCompleteIntersection

/-- Every local dimension in a residue-field fiber of a relative global
complete-intersection presentation equals the presentation dimension. -/
theorem relativeDimensionAt_eq
    {P : Algebra.Presentation R A (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum A) :
    relativeDimensionAt R A q = P.dimension := sorry

/-- For a presentation with `n` generators and `c` relations, every local
dimension in a residue-field fiber equals `n - c`. -/
theorem relativeDimensionAt_eq_natSub
    {P : Algebra.Presentation R A (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum A) :
    relativeDimensionAt R A q = (n - c : WithBot ℕ∞) := sorry

end IsRelativeGlobalCompleteIntersection

end

end Presentation

end Algebra
