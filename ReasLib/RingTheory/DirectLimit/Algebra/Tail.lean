/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.Colimit

/-!
# Tails of directed systems of algebras

Aggregate import for the tail algebra API.  Stage algebra data and algebra
transitions live in `Tail.Core`; tail direct-limit maps and equivalences live
in `Tail.Colimit`.
-/

@[expose] public section
