/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Formal
public import ReasLib.RingTheory.Catenary.Universally

@[expose] public section

/-!
# Universal catenarity from formal catenarity

This leaf contains the failure-direction bridge used in Ratliff's criterion.
The positive implication and the equivalence belong to the later Ratliff owner;
keeping this direction separate gives downstream files a short, stable API.
@stack 0AW3
-/

universe u v

namespace IsFormallyCatenaryRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Lemma 15.110.2 (current Stacks numbering: Lemma 15.111.2, tag `0AW3`):
a Noetherian local ring which is not formally catenary is not universally
catenary. The test universe must contain the universe of the source ring. -/
@[stacks 0AW3 "failure of universal catenarity outside formal catenarity"]
theorem not_universally (hA : ¬ IsFormallyCatenaryRing A) :
    ¬ UniversallyCatenaryRing.{u, max u v} A := sorry
-- Proof strategy: argue contrapositively; universal catenarity makes the required finite-type
-- polynomial and quotient rings catenary, and the completion dimension criterion then supplies
-- `IsFormallyCatenaryRing.iff`.

end IsFormallyCatenaryRing
