/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Bounded
public import ReasLib.RingTheory.Depth

/-!
# Projective dimension over regular local rings

This leaf owns the module-wise homological consequences of regular localness expressed through
module depth, bounded finite free resolutions, and projective dimension. These statements are
useful independently of the Chapter 10 proof route and retain no universe-lift or
restriction-of-scalars implementation details.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace IsRegularLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Proposition 10.110.1 (1), tag 00O7: a finite module over a regular local ring has a bounded
finite free resolution whose length is at most the ring dimension minus the module depth. -/
@[stacks 00O7 "finite free resolution from depth over a regular local ring"]
theorem finiteFreeResolutionLengthLE_of_moduleDepth
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    ChainComplex.FiniteFreeResolution.HasLengthLE R M (d - e) := sorry

/-- Proposition 10.110.1 (1), tag 00O7: the projective-dimension form of the depth bound over a
regular local ring. -/
@[stacks 00O7 "projective dimension from depth over a regular local ring"]
theorem hasProjectiveDimensionLE_of_moduleDepth
    {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e) :
    HasProjectiveDimensionLE (ModuleCat.of R M) (d - e) := sorry

end IsRegularLocalRing
