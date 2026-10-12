/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.QuotientLift.Basic
public import ReasLib.RingTheory.RingHom.QuotientLift.Syntomic
public import ReasLib.RingTheory.RingHom.QuotientLift.Smooth
public import ReasLib.RingTheory.RingHom.QuotientLift.StandardSmooth

@[expose] public section

/-!
# Quotient lifts of algebras

Stable aggregate for property-neutral, syntomic, smooth, and standard-smooth
quotient lifts. Clients should prefer the narrow property leaf they use.
-/
