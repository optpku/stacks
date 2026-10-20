/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.WeaklyContractible.Consequences
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.51.1

Weak contractibility consequences are owned by the generic site API.  The chapter item keeps the
three independent source clauses as recalls and does not install proof-local derived-category or
sections instances.
-/

open CategoryTheory.GrothendieckTopology.IsWeaklyContractible

/- Lemma 21.51.1 (0946) (1): sections over a weakly contractible object form an exact functor. -/
@[stacks 0946 "(1), exact sections over a weakly contractible object"] #check
  @sectionsFunctor_exact

/- Lemma 21.51.1 (0946) (2): positive cohomology over a weakly contractible object vanishes. -/
@[stacks 0946 "(2), higher cohomology vanishing over a weakly contractible object"] #check
  @higherCohomology_isZero

/- Lemma 21.51.1 (0946) (3): every torsor has a section over a weakly contractible object. -/
@[stacks 0946 "(3), torsor sections over a weakly contractible object"] #check
  @torsor_sections_nonempty
