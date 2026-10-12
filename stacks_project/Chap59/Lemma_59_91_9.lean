/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsFinite f]
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Lemma 59.91.9: if `f : X ⟶ Y` is a finite morphism of schemes, then cohomology
commutes with base change for `f`, in the sense of `CohomologyCommutesWithBaseChange`
(cartesian squares, locally torsion abelian étale sheaves, and the degree-`q`
comparisons `higherDirectImage_baseChangeHom` are isomorphisms). -/
@[stacks 0A4E]
theorem cohomologyCommutesWithBaseChange_of_isFinite :
    CohomologyCommutesWithBaseChange f := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
