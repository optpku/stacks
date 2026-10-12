/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GlobalDimension.Basic

/-!
# Global dimension of regular local rings

This leaf packages the ring-level consequence of the regular-local module-depth bound. The
module-wise projective-dimension theorem remains in the lighter ProjectiveDimension leaf.
-/

@[expose] public section

universe u

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Proposition 10.110.1 (2), tag 00O7: a regular local ring has global dimension bounded by its
Krull dimension. -/
@[stacks 00O7 "global dimension of a regular local ring"]
theorem hasGlobalDimensionLE_of_ringKrullDim
    {d : ℕ} (hdim : ringKrullDim R = d) :
    HasGlobalDimensionLE R d := sorry

end IsRegularLocalRing
