/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.Gorenstein.Ring

@[expose] public section

universe u v

namespace RingHom.IsLocalCompleteIntersection

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- A local complete-intersection homomorphism from a Gorenstein ring has Gorenstein target. -/
@[stacks 0DWA]
theorem isGorensteinRing [IsGorensteinRing A] {f : A →+* B}
    (h : f.IsLocalCompleteIntersection) : IsGorensteinRing B := sorry

end RingHom.IsLocalCompleteIntersection
