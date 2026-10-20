/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Tail.Core
public import ReasLib.RingTheory.DirectLimit.Tail.Properties
public import ReasLib.RingTheory.DirectLimit.Tail.Colimit

/-!
# Tails of directed ring direct limits

Aggregate import for the tail comparison API.  The core maps, representation
properties, and transport to a chosen colimit are available independently from
their corresponding leaf modules.
-/

@[expose] public section

/- The declarations live in `Tail.Core`, `Tail.Properties`, and
`Tail.Colimit`; this file is the stable aggregate import. -/
