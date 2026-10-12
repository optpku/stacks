/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.Kunneth.Dedekind
import StacksCheckRecall

/-!
# Example 15.64.5

@stack 0H80
-/

@[expose] public section

/- Example 15.64.5 (1): higher `Tor` over a Dedekind domain vanishes above degree one. -/
@[stacks 0H80 "Example 15.64.5 (1)"]
#check @CategoryTheory.Kunneth.torIsZeroAboveOne

/- Example 15.64.5 (2): the bounded Künneth spectral sequence degenerates at `E₂`. -/
@[stacks 0H80 "Example 15.64.5 (2)"]
#check @CategoryTheory.Kunneth.degeneratesAtTwo

/- Example 15.64.5 (3): the two surviving columns give the Künneth short exact sequence. -/
@[stacks 0H80 "Example 15.64.5 (3)"]
#check @CategoryTheory.Kunneth.existsShortExactSequence
