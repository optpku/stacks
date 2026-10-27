/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.OverField.FieldExtension
public import ReasLib.RingTheory.RingHom.Syntomic.Basic

@[expose] public section

/-!
# Syntomic Algebras over a Field

This leaf connects field-relative local complete intersections to the
ring-homomorphism fiber and syntomic predicates.
-/

universe u v

namespace IsLocalCompleteIntersection

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

/-- A residue-field fiber of a local complete-intersection algebra over a
field is again a local complete intersection. -/
@[stacks 00SL "field fibers of local complete intersections"]
theorem fiber [IsLocalCompleteIntersection k A] (p : PrimeSpectrum k) :
    IsLocalCompleteIntersection p.asIdeal.ResidueField
      (p.asIdeal.Fiber A) := sorry

/-- The structure map of a local complete-intersection algebra over a field
has local complete-intersection fibers. -/
@[stacks 00SL "local complete-intersection fibers over a field"]
theorem hasLocalCompleteIntersectionFibers [IsLocalCompleteIntersection k A] :
    (algebraMap k A).HasLocalCompleteIntersectionFibers := sorry

/-- A local complete-intersection algebra over a field has a syntomic
structure map. -/
@[stacks 00SL "local complete intersections over a field are syntomic"]
theorem syntomic [IsLocalCompleteIntersection k A] :
    (algebraMap k A).Syntomic := sorry

end IsLocalCompleteIntersection
