/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.Limit.Basic
import StacksCheckRecall

@[expose] public section

/-
Lemma 5.24.2 is a source-facing check of the cofiltered nonemptiness results in the neutral spectral
inverse-limit API.
-/

/- Lemma 5.24.2 (1): stable nonempty constructibly closed subspaces have nonempty inverse limit. -/
@[stacks 0A2W "stable nonempty constructibly closed subsets"]
#check nonempty_limit_of_constructibleClosed_stableSubsetDiagram

/- Lemma 5.24.2 (2): a cofiltered diagram of nonempty spectral spaces has nonempty inverse limit. -/
@[stacks 0A2W "nonempty ambient inverse limit"]
#check nonempty_limit_of_spectralSpaceDiagram
