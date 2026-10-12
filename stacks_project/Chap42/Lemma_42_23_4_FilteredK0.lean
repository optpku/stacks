/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FilteredK0

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GradedK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Compatibility check for the canonical transition from the degree-`k` graded
Grothendieck group to the wider filtered Grothendieck group. -/
#check
  (AlgebraicGeometry.Scheme.Modules.GradedK0.toFilteredK0 f δ k :
    AlgebraicGeometry.Scheme.Modules.GradedK0 f δ k →+
      AlgebraicGeometry.Scheme.Modules.FilteredK0 f δ (k + 1) (k - 1))

end AlgebraicGeometry.Scheme.Modules.GradedK0
