/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsProper f] [IsProper g] [Surjective f]
variable [∀ W : Scheme.{u}, HasSheafify W.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ W : Scheme.{u},
    HasInjectiveResolutions (Sheaf W.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Lemma 59.91.7: if `f : X ⟶ Y` and `g : Y ⟶ Z` are proper morphisms of schemes,
cohomology commutes with base change for `f` and for `g ∘ f` (i.e. `f ≫ g`),
and `f` is surjective, then cohomology commutes with base change for `g`. -/
@[stacks 0A4C]
theorem cohomologyCommutesWithBaseChange_of_comp
    (hf : CohomologyCommutesWithBaseChange f)
    (hgf : CohomologyCommutesWithBaseChange (f ≫ g)) :
    CohomologyCommutesWithBaseChange g := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
