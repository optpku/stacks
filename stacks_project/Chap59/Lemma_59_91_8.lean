/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsProper f] [IsProper g]
variable [∀ W : Scheme.{u}, HasSheafify W.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ W : Scheme.{u},
    HasInjectiveResolutions (Sheaf W.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Lemma 59.91.8: if `f : X ⟶ Y` and `g : Y ⟶ Z` are proper morphisms of schemes
and cohomology commutes with base change for each of `f` and `g`, then cohomology
commutes with base change for the composite `g ∘ f`, written `f ≫ g` in Lean. -/
@[stacks 0A4D]
theorem cohomologyCommutesWithBaseChange_comp
    (hf : CohomologyCommutesWithBaseChange f)
    (hg : CohomologyCommutesWithBaseChange g) :
    CohomologyCommutesWithBaseChange (f ≫ g) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
