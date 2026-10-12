/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Noetherian
import StacksCheckRecall

/-!
# Lemma 15.45.3

@stack 06LJ
-/

@[expose] public section

/-! # Lemma 15.45.3: Noetherianity and henselization -/

/- Lemma 15.45.3, equivalence (1)-(3): a local ring is Noetherian exactly when a henselization,
or a strict henselization, is Noetherian. -/
@[stacks 06LJ "equivalence (1)-(3), Noetherianity is invariant under henselization"]
#check @Henselization.noetherian_tfae

/- Lemma 15.45.3 (a): the completions of the henselization and strict henselization are
Noetherian complete local rings. -/
@[stacks 06LJ "(a) completed henselizations"]
#check @Henselization.completions_noetherian_complete_local

/- Lemma 15.45.3 (b): the base completion and henselization completion are canonically
isomorphic. -/
@[stacks 06LJ "(b) henselization completion comparison"]
#check @IsHenselizationOf.Completion.map_bijective

/- Lemma 15.45.3 (c): both henselization-to-completion maps are flat. -/
@[stacks 06LJ "(c) flat completion maps"]
#check @Henselization.completion_algebraMaps_flat

/- Lemma 15.45.3 (d): the map from the base completion to the strict-henselization completion is
formally smooth in the target maximal-ideal topology. -/
@[stacks 06LJ "(d) formal smoothness of the strict completion map"]
#check @Henselization.strictCompletionMap_formallySmooth

/- Lemma 15.45.3 (e): the strict henselization of the base completion is the canonical tensor
base change of the chosen strict henselization. -/
@[stacks 06LJ "(e) strict henselization after completion"]
#check @Henselization.strictBaseChange_isStrictHenselization

/- Lemma 15.45.3 (f): completing that strict base-change model recovers the strict-henselization
completion. -/
@[stacks 06LJ "(f) completion of the strict base-change model"]
#check @Henselization.strictBaseChange_completionMap_bijective

#check @IsHenselizationOf.isNoetherianRing
#check @IsStrictHenselizationOf.isNoetherianRing
#check @Henselization.strictBaseChange_includeRight_isLocal
