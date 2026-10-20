/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap84.Lemma_84_6_4_Comparison
public import stacks_project.Chap84.Lemma_84_6_6_InverseImage

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Comparison

/-! # Compatibility checks for fppf and étale direct image of algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.epsilonPushforward :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.epsilonPushforward_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    epsilonPushforward X = comparisonTopologyPushforwardAb etale_le_fppf X)

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.aInverse_unit :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    (etalePiInverseImage X).obj F ⟶
      (epsilonPushforward X).obj ((aInverseAb X).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.aInverse_unit_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    aInverse_unit X F =
      (comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_fppf X).unit.app
        ((etalePiInverseImage X).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.aInverse_unit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    IsIso (aInverse_unit X F))

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.epsilonPushforward_hasRightDerivedFunctor :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (epsilonPushforward X).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1})))

end
