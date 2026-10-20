/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Colimit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Properties

/-!
# Tails of directed algebra approximations

Aggregate import for the tail API.  Core restriction data, colimit transport,
base-change computations, and optional property instances are separate leaves.
-/

@[expose] public section

/- The declarations live in `Tail.Core`, `Tail.Colimit`, `Tail.BaseChange`, and
`Tail.Properties`; this file is the stable aggregate import. -/
