/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.ProjectiveSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Lemma 59.91.10: to prove that cohomology commutes with base change for every
proper morphism of schemes, it suffices to prove `CohomologyCommutesWithBaseChange`
for the structure morphism `ProjectiveSpace.toBase 1 S : ProjectiveSpace 1 S ⟶ S`
of the relative projective line, for every scheme `S`. -/
@[stacks 0A4F]
theorem cohomologyCommutesWithBaseChange_of_projectiveLine
    (hP1 : ∀ S : Scheme.{u}, CohomologyCommutesWithBaseChange (toBase 1 S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange f := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
