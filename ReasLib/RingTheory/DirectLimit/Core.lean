/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra
public import ReasLib.RingTheory.DirectLimit.Comparison
public import ReasLib.RingTheory.DirectLimit.Constant
public import ReasLib.RingTheory.DirectLimit.Domain
public import ReasLib.RingTheory.DirectLimit.Lift
public import ReasLib.RingTheory.DirectLimit.Local
public import ReasLib.RingTheory.DirectLimit.Module.FinitePresentation
public import ReasLib.RingTheory.DirectLimit.Module.Transport
public import ReasLib.RingTheory.DirectLimit.Reindex
public import ReasLib.RingTheory.DirectLimit.Tail

/-!
# Core API for ring direct limits

This aggregate exposes the neutral direct-system, comparison, local-ring, and
module-transport infrastructure.  Higher-level approximation and base-change
applications remain in their own leaves, so foundational consumers can import
this module without pulling in those applications.
-/

@[expose] public section
