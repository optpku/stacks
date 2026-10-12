/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.6.3: the affine comparison identifies a scheme basic open with
the corresponding principal open of its global-section spectrum. -/
@[stacks 01I0] #check Scheme.map_PrimeSpectrum_basicOpen_of_affine

/- General companion: the same basic-open equality holds for the canonical map to the spectrum
of global sections without assuming the scheme affine. -/
#check Scheme.toSpecΓ_preimage_basicOpen
