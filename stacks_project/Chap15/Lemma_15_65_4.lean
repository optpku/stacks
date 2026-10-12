/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Module
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.65.4

The module-level pseudo-coherence criteria in terms of finiteness, finite presentation, and
finite-free resolutions are owned by `ModuleCat.IsMPseudoCoherent` and
`ModuleCat.IsPseudoCoherent`.

@stack 064T
-/

/- Lemma 15.65.4 (1): `0`-pseudo-coherent modules are exactly finite modules. -/
@[stacks 064T "Lemma 15.65.4 (1)"]
#check @CategoryTheory.ModuleCat.IsMPseudoCoherent.zero_iff_finite

/- Lemma 15.65.4 (2): `(-1)`-pseudo-coherent modules are exactly finitely presented modules. -/
@[stacks 064T "Lemma 15.65.4 (2)"]
#check @CategoryTheory.ModuleCat.IsMPseudoCoherent.minusOne_iff_finitePresentation

/- Lemma 15.65.4 (3): a `(-d)`-pseudo-coherence bound is characterized by a finite-free
resolution of length `d`. -/
@[stacks 064T "Lemma 15.65.4 (3)"]
#check @CategoryTheory.ModuleCat.IsMPseudoCoherent.neg_iff_hasLengthFiniteFreeResolution

/- Lemma 15.65.4 (4): pseudo-coherence is characterized by an infinite finite-free
resolution. -/
@[stacks 064T "Lemma 15.65.4 (4)"]
#check @CategoryTheory.ModuleCat.IsPseudoCoherent.iff_exists_finiteFreeResolution

#check @CategoryTheory.ModuleCat.IsMPseudoCoherent.of_finiteFree
#check @CategoryTheory.ModuleCat.IsPseudoCoherent.of_finiteFreeResolution

end
