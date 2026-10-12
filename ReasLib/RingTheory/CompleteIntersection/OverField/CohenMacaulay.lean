/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.CompleteIntersection.OverField.Localization

@[expose] public section

/-!
# Cohen-Macaulay Complete Intersections over a Field

The intrinsic local-complete-intersection predicate is the owner of the
Cohen-Macaulay consequence.  No presentation choice or localization witness
is exposed to downstream users.
-/

universe u v

namespace IsLocalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- Lemma 10.135.3, tag `00SB`: a local complete intersection over a field is
a Cohen-Macaulay ring. -/
@[stacks 00SB "local complete intersections over a field are Cohen-Macaulay"]
theorem cohenMacaulayRing (hS : IsLocalCompleteIntersection k S) :
    CohenMacaulayRing S := sorry

end IsLocalCompleteIntersection
