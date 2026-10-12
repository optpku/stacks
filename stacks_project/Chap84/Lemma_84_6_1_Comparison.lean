/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap84.Lemma_84_6_4_Comparison
public import stacks_project.Chap84.Lemma_84_6_6_InverseImage

/-!
# Fppf/étale direct image of algebraic spaces

This leaf owns the abelian identity-site direct image `ε_{X,*}`, the canonical
comparison map `π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)`, and the bounded-below right-derived
floor for `ε_{X,*}`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

variable {S : Scheme.{u}}

/-- Direct image `ε_{X,*}` on abelian sheaves from the big fppf slice to the big étale slice. -/
abbrev epsilonPushforward (X : AlgebraicSpace S) :
    Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPushforwardAb etale_le_fppf X

/-- `epsilonPushforward` is the abelian topology-comparison direct image. -/
theorem epsilonPushforward_eq (X : AlgebraicSpace S) :
    epsilonPushforward X = comparisonTopologyPushforwardAb etale_le_fppf X := sorry

/-- The canonical comparison map `π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)`. -/
def aInverse_unit (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (etalePiInverseImage X).obj F ⟶
      (epsilonPushforward X).obj ((aInverseAb X).obj F) :=
  (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X).unit.app
    ((etalePiInverseImage X).obj F)

/-- `aInverse_unit` is the topology-comparison adjunction unit at `π_X⁻¹ F`. -/
theorem aInverse_unit_eq (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    aInverse_unit X F =
      (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X).unit.app
        ((etalePiInverseImage X).obj F) := sorry

/-- For an abelian sheaf `F` on `X_étale`, the canonical map
`π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
theorem aInverse_unit_isIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    IsIso (aInverse_unit X F) := sorry

/-- The bounded-below right-derived functor of `ε_{X,*}` exists. -/
instance epsilonPushforward_hasRightDerivedFunctor (X : AlgebraicSpace S) :
    (epsilonPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1})) := sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
