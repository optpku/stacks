/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

Adapted from MichaelStollBayreuth/EllipticCurves at
4c43c4089d2960904c0a4c1bb4668e827d80a62d.
Source fragments: Basic.lean:147-151, SelmerGroup.lean:98-166.
Changes: relocated general group infrastructure to its mathematical owner;
declaration names, hypotheses, and proof bodies are preserved.
The upstream files have no per-file copyright header; repository license and author retained.
-/
module

public import ReasLib.Algebra.Group.Units.ModPow
public import ReasLib.GroupTheory.Finiteness.Abelian

/-!
# Compatibility imports for power classes

The general group lemmas are owned by `ReasLib.GroupTheory.Finiteness` and
`ReasLib.GroupTheory.Finiteness.Abelian`; the units quotient abbreviation is
owned by `ReasLib.Algebra.Group.Units.ModPow`. This legacy path publicly
re-exports their API for existing Selmer consumers and declares no new data.
-/
