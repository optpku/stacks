/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConstructibleTopology.Spectral
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 5.23.2 (1): the constructible topology of a spectral space is
Hausdorff. -/
@[stacks 0901 "Hausdorffness"]
#check constructibleTopology_t2Space

/- Lemma 5.23.2 (2): the constructible topology of a spectral space is totally
disconnected. -/
@[stacks 0901 "total disconnectedness"]
#check constructibleTopology_totallyDisconnectedSpace

/- Lemma 5.23.2 (3): the constructible topology of a spectral space is
compact. -/
@[stacks 0901 "quasi-compactness"]
#check fun {X : Type u} [TopologicalSpace X] [SpectralSpace X] ↦
  (compactSpace_withConstructibleTopology (X := X) : CompactSpace (WithConstructibleTopology X))
