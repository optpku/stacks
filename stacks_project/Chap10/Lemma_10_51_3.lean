/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Filtration.ArtinRees.LinearMap
import StacksCheckRecall

/-!
# Lemma 10.51.3

@stack 00IO
-/

@[expose] public section

/- Lemma 10.51.3, tag `00IO`: an exact sequence into a finite module over a Noetherian ring
admits one Artin-Rees constant controlling both inverse images and image intersections. -/
@[stacks 00IO]
#check @Ideal.exists_artin_rees_constant_of_exact

@[stacks 00IO "Artin-Rees bound predicate"]
#check @LinearMap.IsArtinReesBound

@[stacks 00IO "preimage-power Artin-Rees bound"]
#check @LinearMap.isArtinReesBound_of_preimage_pow_smul_eq

@[stacks 00IO "exact preimage power equality"]
#check @Ideal.exists_exact_preimage_pow_smul_eq
