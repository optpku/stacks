/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Catenary.Universally

/-!
# Universal catenarity of fields

This module owns the canonical universal-catenarity instance for fields.
-/

@[expose] public section

universe u v

/-- Every field is universally catenary. -/
@[stacks 00NM "field specialization"]
instance instUniversallyCatenaryRingOfField {K : Type u} [Field K] :
    UniversallyCatenaryRing.{u, v} K := sorry

namespace IsCatenaryRing

/-- Every finite type algebra over a field is catenary. -/
theorem of_finiteType_over_field (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : IsCatenaryRing A :=
  UniversallyCatenaryRing.catenary_of_finiteType k

end IsCatenaryRing
