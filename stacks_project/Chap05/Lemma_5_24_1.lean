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
Lemma 5.24.1 is a source-facing check of the neutral spectral inverse-limit API: first for a transition-stable
family of constructibly closed subspaces, then for the ambient spectral diagram.
-/

/- Lemma 5.24.1 (1): stable constructibly closed subspaces have compact inverse limit. -/
@[stacks 0A2V "stable constructibly closed subsets"]
#check compactSpace_limit_of_constructibleClosed_stableSubsetDiagram

/- Lemma 5.24.1 (2): a spectral diagram with spectral maps has compact inverse limit. -/
@[stacks 0A2V "ambient inverse limit"]
#check compactSpace_limit_of_spectralSpaceDiagram
