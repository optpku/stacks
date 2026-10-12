/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Point.FiniteSeparable
import StacksCheckRecall

/-!
# Étale neighborhoods realizing finite separable residue extensions

@stack 00UD

The constructed algebra and selected prime are retained by the canonical
`PrimeSpectrum.EtalePoint` data owner.
-/

@[expose] public section

@[stacks 00UD "source bridge"]
#check @PrimeSpectrum.EtalePoint.exists_with_residueFieldEquiv

@[stacks 00UD "pointed etale data owner"]
#check @PrimeSpectrum.EtalePoint.spec
