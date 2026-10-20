/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normalization.OneDimensional.Completion
public import ReasLib.RingTheory.Normalization.OneDimensional.Henselization

/-!
# Delta invariant under local normalization operations

This leaf supplies the equality API for the normalization delta invariant under
henselization, strict henselization, and maximal-ideal completion in dimension
one.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Normalization.OneDimensional

namespace Henselization

variable {A : Type u} {Ah : Type v}
variable [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- Henselization preserves the normalization delta invariant of a reduced Nagata
one-dimensional local ring. -/
@[stacks 0C3W]
theorem deltaInvariant_eq (h_dimension : ringKrullDim A = 1) :
    deltaInvariant A = deltaInvariant Ah := sorry

end Henselization

namespace StrictHenselization

variable {A : Type u} {Ash : Type v}
variable [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- Strict henselization preserves the normalization delta invariant of a reduced Nagata
one-dimensional local ring. -/
@[stacks 0C3W]
theorem deltaInvariant_eq (h_dimension : ringKrullDim A = 1) :
    deltaInvariant A = deltaInvariant Ash := sorry

end StrictHenselization

namespace Completion

variable {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]

/-- Completion at the maximal ideal preserves the normalization delta invariant of a
reduced Nagata one-dimensional local ring. -/
@[stacks 0C3W]
theorem deltaInvariant_eq (h_dimension : ringKrullDim A = 1) :
    deltaInvariant A = deltaInvariant (AdicCompletion (maximalIdeal A) A) := sorry

end Completion

end Normalization.OneDimensional
