/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.Local.Regularity

/-!
# Regularity of smooth algebras over fields

This leaf is the global form of the local regularity theorem for smooth
algebras over a field.
-/

@[expose] public section

universe u v

namespace Algebra.Smooth

/-- A smooth algebra over a field is a regular ring. -/
@[stacks 00TT "regularity of smooth algebras over fields"]
theorem isRegularRing_of_field
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] [Algebra.Smooth k S] :
    IsRegularRing S := sorry

end Algebra.Smooth
