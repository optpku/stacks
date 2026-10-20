/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower.Tame
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.113.10

@stack 0BU7

This entry recalls the canonical restriction and comparison maps for a finite Galois tower.  The
maps, residue-field transport, and character squares are owned by `integralClosure.Tower`; this
file does not install a second algebra, action, or selected inverse.
-/

namespace Lemma_15_113_10

/- Lemma 15.113.10 (1): restriction on decomposition groups is surjective. -/
@[stacks 0BU7 "Lemma 15.113.10 (1): decomposition-group restriction surjectivity"]
#check (@integralClosure.Tower.decompositionHom_surjective)

/- Lemma 15.113.10 (2): restriction on inertia groups is surjective. -/
@[stacks 0BU7 "Lemma 15.113.10 (2): inertia-group restriction surjectivity"]
#check (@integralClosure.Tower.inertiaHom_surjective)

/- Lemma 15.113.10 (3): restriction on wild inertia groups is surjective. -/
@[stacks 0BU7 "Lemma 15.113.10 (3): wild-inertia restriction surjectivity"]
#check (@integralClosure.Tower.wildInertiaHom_surjective)

/- Lemma 15.113.10 (4): the induced residue-field action square commutes. -/
@[stacks 0BU7 "Lemma 15.113.10 (4): residue-action comparison square"]
#check (@integralClosure.Tower.decompositionHom_residueMap)

/- Lemma 15.113.10 (5): the lower ramification index divides the upper one. -/
@[stacks 0BU7 "Lemma 15.113.10 (5): ramification-index divisibility"]
#check (@integralClosure.Tower.ramificationIdxIn_dvd)

/- Lemma 15.113.10 (6): the tame inertia order divides along the tower. -/
@[stacks 0BU7 "Lemma 15.113.10 (6): tame-inertia order divisibility"]
#check (@integralClosure.Tower.tameInertiaCard_dvd)

/- Lemma 15.113.10 (7): the roots-of-unity power map compares the two ramification indices. -/
@[stacks 0BU7 "Lemma 15.113.10 (7): ramification power map"]
#check (@integralClosure.Tower.Tame.ramificationPower)

/- Lemma 15.113.10 (8): the unscaled tame-character square commutes. -/
@[stacks 0BU7 "Lemma 15.113.10 (8): tame-character comparison square"]
#check (@integralClosure.Tower.Tame.character_naturality)

/- Lemma 15.113.10 (9): pointwise form of the unscaled tame-character square. -/
@[stacks 0BU7 "Lemma 15.113.10 (9): pointwise tame-character comparison"]
#check (@integralClosure.Tower.Tame.character_naturality_apply)

end Lemma_15_113_10
