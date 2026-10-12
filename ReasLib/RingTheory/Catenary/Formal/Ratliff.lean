/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Formal.Universal
public import ReasLib.RingTheory.Catenary.Formal.ToUniversal

@[expose] public section

/-!
# Ratliff's formal-catenarity criterion

This leaf owns the equivalence between the intrinsic formal-catenarity
condition and universal catenarity for a local ring.  The two implications
are kept as separate reusable bridges in the neighboring leaves; this file
only exposes their canonical equivalence and does not create a reverse
typeclass instance.
@stack 0AW6
-/

universe u v

namespace UniversallyCatenaryRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Proposition 15.110.5 (current Stacks numbering: Proposition 15.111.5,
Ratliff, tag `0AW6`): a Noetherian local ring is universally catenary if and
only if it is formally catenary. -/
@[stacks 0AW6 "Ratliff formal/universal catenarity equivalence"]
theorem iff_formallyCatenary :
    UniversallyCatenaryRing.{u, v} A ↔ IsFormallyCatenaryRing A := by
  constructor
  · intro hA
    exact Classical.byContradiction fun hformal ↦
      (IsFormallyCatenaryRing.not_universally hformal) hA
  · intro hA
    letI : IsFormallyCatenaryRing A := hA
    infer_instance
-- Proof strategy: for the forward direction use the contrapositive
-- `IsFormallyCatenaryRing.not_universally`; for the reverse direction install the formal
-- catenarity evidence and use `IsFormallyCatenaryRing.toUniversallyCatenaryRing`.

end UniversallyCatenaryRing
