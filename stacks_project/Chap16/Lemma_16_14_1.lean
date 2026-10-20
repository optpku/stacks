/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Approximation.Artin.Henselian
import StacksCheckRecall

@[expose] public section

/- Lemma 16.14.1, G-ring branch. -/
@[stacks 0AH5 "G-ring branch"]
#check @HenselianRing.ArtinApproximation.nonempty_of_isGRing

/- Lemma 16.14.1, pair-henselization branch. -/
@[stacks 0AH5 "pair henselization branch"]
#check @HenselianRing.ArtinApproximation.nonempty_of_pair

/- Lemma 16.14.1, regular completion-map core. -/
@[stacks 0AH5 "regular completion-map core"]
#check @HenselianRing.ArtinApproximation.nonempty
#check @MvPolynomial.IsSolution
#check @MvPolynomial.SolutionApproximation
#check @IsPairHenselization.isGRing
#check @IsPairHenselization.AdicCompletion.regularMap
