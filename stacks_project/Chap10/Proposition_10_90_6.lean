/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Coherent.Products
import StacksCheckRecall

/-!
# Proposition 10.90.6

@stack 05CZ
-/

@[expose] public section

/- Proposition 10.90.6: coherence of `R`, flatness of arbitrary products of flat `R`-modules,
and flatness of every power `A → R` are equivalent. -/
@[stacks 05CZ]
#check @IsCoherentRing.tfae_flat_products

@[stacks 05CZ "flat products over a coherent ring"]
#check @IsCoherentRing.piFlat
@[stacks 05CZ "flat powers characterize coherence"]
#check @IsCoherentRing.iff_piSelf_flat
