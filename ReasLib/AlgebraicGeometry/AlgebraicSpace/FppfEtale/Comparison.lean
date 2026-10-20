/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf and étale sheaf comparison for algebraic spaces

The canonical comparison units identify small étale sheaves with their fppf
pullbacks after direct image. Abelian small étale sheaves have fppf pullbacks
with vanishing positive-degree higher comparison direct images.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn

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
    epsilonPushforward X = comparisonTopologyPushforwardAb etale_le_fppf X := rfl

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
        ((etalePiInverseImage X).obj F) := rfl

/-- For an abelian sheaf `F` on `X_étale`, the canonical map
`π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
instance aInverse_unit_isIso {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    IsIso (aInverse_unit X F) := sorry

/-- The bounded-below right-derived functor of `ε_{X,*}` exists. -/
instance epsilonPushforward_hasRightDerivedFunctor (X : AlgebraicSpace S) :
    (epsilonPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1})) := sorry


/-- For a sheaf of sets `F` on `X_étale`, the canonical map
`π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
@[stacks 0DGF]
instance epsilon_pushforward_aInverse_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((Fppf.epsilon X).adjunction.unit.app ((siteMorphismOfTopoi X)⁻¹.obj F)) :=
  sorry

/-- For a sheaf of sets `F` on `X_étale`, the canonical map
`F ⟶ a_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
@[stacks 0DGF]
instance fppfComparison_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((fppfComparison X).adjunction.unit.app F) := sorry

/-- For an abelian sheaf `F` on `X_étale` and `0 < i`, the higher
direct images `R^i ε_{X,*}(a_X⁻¹ F)` vanish. -/
@[stacks 0DGF]
theorem aInverse_higherDirectImage_isZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ) (hi : 0 < i) :
    IsZero (((epsilonPushforward X).rightDerived i).obj ((aInverseAb X).obj F)) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
