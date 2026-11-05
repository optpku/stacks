/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Spectral.Basic
public import ReasLib.Topology.IrreducibleCloseds.Soberification.Basic

/-!
# Topological Properties of the Irreducible-Closed Soberification

This module transfers compactness, spectrality, and Noetherianity to the
soberification carried by `IrreducibleCloseds X`.
-/

@[expose] public section

universe u

open TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IrreducibleCloseds

/-- Lemma 5.23.15 (1): the irreducible-closed soberification of a compact
space is compact. -/
@[stacks 0A2T "compact soberification"]
instance compactSpaceSoberification [CompactSpace X] :
    CompactSpace (IrreducibleCloseds X) := sorry

/-- Lemma 5.23.15 (2): the irreducible-closed soberification of a compact,
prespectral, quasi-separated space is spectral. -/
@[stacks 0A2T "spectral soberification"]
instance spectralSpaceSoberification [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] : SpectralSpace (IrreducibleCloseds X) := sorry

/-- Lemma 5.23.15 (3): the irreducible-closed soberification of a Noetherian
space is Noetherian. -/
@[stacks 0A2T "Noetherian soberification"]
instance noetherianSpaceSoberification [NoetherianSpace X] :
    NoetherianSpace (IrreducibleCloseds X) := sorry

end TopologicalSpace.IrreducibleCloseds
