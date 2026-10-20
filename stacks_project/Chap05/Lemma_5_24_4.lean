/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Limit.Constructible
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.24.4 recalls the neutral stagewise-descent API for constructible subsets of cofiltered
spectral inverse limits.
-/

/- Lemma 5.24.4 (1): constructible subsets descend from one stage. -/
@[stacks 0A2Y "constructible subsets descend"]
#check constructible_eq_preimage_of_isLimit

/- Lemma 5.24.4 (2): open constructible subsets descend as compact opens. -/
@[stacks 0A2Y "open constructible subsets descend as compact opens"]
#check open_eq_preimage_of_isLimit_of_isConstructible

/- Lemma 5.24.4 (3): closed constructible subsets descend as closed constructible sets. -/
@[stacks 0A2Y "closed constructible subsets descend as closed constructible sets"]
#check closed_eq_preimage_of_isLimit_of_isConstructible
