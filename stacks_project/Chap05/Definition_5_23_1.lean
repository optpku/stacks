/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Spectral.Basic
public import ReasLib.Topology.Maps.Spectral.Characterization
import StacksCheckRecall

@[expose] public section

/- Definition 5.23.1 (1): `SpectralSpace` is Mathlib's canonical owner for
spectral topological spaces. -/
@[stacks 08YG "spectral topological spaces"]
#check SpectralSpace

/- Definition 5.23.1 (2): `IsSpectralMap` is the canonical map predicate, and
the ReasLib characterization presents its textbook form. -/
@[stacks 08YG "spectral maps"]
#check IsSpectralMap.iff_continuous_and_isCompact_preimage_of_isOpen
