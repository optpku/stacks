/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RegularLocalRing.ProjectiveDimension
public import ReasLib.RingTheory.RegularLocalRing.GlobalDimension
import StacksCheckRecall

/-!
# Homological bounds for regular local rings

The reusable depth, projective-dimension, finite-free-resolution, and global-dimension results are
owned by ReasLib. This chapter file recalls the two source clauses without introducing aliases.

@stack 00O7
-/

@[expose] public section

universe u v

open CategoryTheory ChainComplex

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {d e : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = e)

/- Proposition 10.110.1 (1): if `R` is a regular local ring of dimension `d` and `M` is a finite
`R`-module of depth `e`, then `M` admits a finite free resolution of length at most `d - e`. -/
@[stacks 00O7 "(1)"]
#check (IsRegularLocalRing.finiteFreeResolutionLengthLE_of_moduleDepth hdim hdepth :
  ChainComplex.FiniteFreeResolution.HasLengthLE R M (d - e))

/- The corresponding projective-dimension statement is the canonical companion to clause (1). -/
#check (IsRegularLocalRing.hasProjectiveDimensionLE_of_moduleDepth hdim hdepth :
  HasProjectiveDimensionLE (ModuleCat.of R M) (d - e))

/- Proposition 10.110.1 (2): a regular local ring of dimension `d` has global dimension at most
`d`. -/
@[stacks 00O7 "(2)"]
#check (IsRegularLocalRing.hasGlobalDimensionLE_of_ringKrullDim hdim :
  HasGlobalDimensionLE R d)

end
