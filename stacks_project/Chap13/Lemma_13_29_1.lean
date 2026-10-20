/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Truncation.UpperResolution.Functoriality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.29.1

The upper-truncation diagram and its property-neutral resolution tower are
owned by ReasLib.  The construction uses the same namespace and interface
shape as the dual lower-truncation resolution.
-/

/- Lemma 13.29.1 (Stacks 06XX) (1): the canonical upper truncations form a sequential direct
system using the general comparison between two truncation cutoffs. -/
@[stacks 06XX]
#check @CochainComplex.UpperTruncation.diagram

/- The canonical upper-truncation diagram is functorial in the input complex, with componentwise
maps given by `CochainComplex.truncLEMap`. -/
@[stacks 06XX]
#check @CochainComplex.UpperTruncation.diagramFunctor

/- Lemma 13.29.1 (Stacks 06XX) (2): the reusable resolution owner records stagewise bounded
termwise-`P` quasi-isomorphisms and split-monic transitions with cokernels in `P`. -/
@[stacks 06XX]
#check @CochainComplex.UpperTruncation.Resolution

/- Lemma 13.29.1 (Stacks 06XX) (3): every complex admits such a tower under the zero,
finite-coproduct, and epimorphic-cover hypotheses on `P`. -/
@[stacks 06XX]
#check @CochainComplex.UpperTruncation.exists_resolution

/- Supporting colimit-facing API: every resolution carries a canonical cocone and comparison
from its sequential colimit to the original complex. -/
@[stacks 06XX]
#check @CochainComplex.UpperTruncation.Resolution.fromColimit
