/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Idempotents.Karoubi

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents

universe w v u

/-- The category of Chow motives over a field `k`, modeled as the Karoubi envelope of
the category `GradedCorrespondence k` whose objects include the integral degree shift. -/
abbrev ChowMotive (k : Type u) [Field k]
    (GradedCorrespondence : Type u → Type v)
    [Category.{w} (GradedCorrespondence k)] :=
  Karoubi (GradedCorrespondence k)

namespace ChowMotive

/-- The category of Chow motives modeled by a Karoubi envelope is idempotent complete. -/
theorem isIdempotentComplete (k : Type u) [Field k]
    (GradedCorrespondence : Type u → Type v)
    [Category.{w} (GradedCorrespondence k)] :
    IsIdempotentComplete (ChowMotive k GradedCorrespondence) :=
  inferInstance

end ChowMotive
