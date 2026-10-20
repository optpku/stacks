/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Lift
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.19.11

The source-facing lifting result is the bounded-projective specialization of the neutral
K-projective lifting API.  Its mapping-cone vanishing input is exposed separately for reuse.
-/

/- Lemma 13.19.11: the isomorphism-above and epimorphism-at hypotheses force mapping-cone
cohomology to vanish from the bound onward. -/
#check @CochainComplex.MappingCone.Homology.isZero_of_iso_epi

/- Lemma 13.19.11: a bounded-above projective complex supported from the bound admits the
required lift up to cochain homotopy. -/
@[stacks 064E] #check @CochainComplex.ProjectiveMinus.existsHomotopyLift
