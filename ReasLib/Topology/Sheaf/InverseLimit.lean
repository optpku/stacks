/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.InverseLimit.System
public import ReasLib.Topology.Sheaves.InverseLimit.PullbackSections
public import ReasLib.Topology.Sheaf.InverseLimit.FinitePresentation

/-!
# Sheaf systems on inverse limits

Canonical entry point for sheaf systems on inverse limit diagrams:
- `SheafSystem` — compatible sheaves on stages of an inverse system
- `PullbackSections` — section comparison for pullback in inverse systems
- `CompactOpenPresentation` — finite-stage models of finitely presented sheaves on spectral spaces
-/
