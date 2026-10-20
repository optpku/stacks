/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
public import stacks_project.Chap84.Lemma_84_5_5_SmallToBig
public import stacks_project.Chap84.Lemma_84_6_6_InverseImage
public import stacks_project.Chap84.Lemma_84_8_4_Comparison

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.InverseImage

/-! # Compatibility checks for abelian ph inverse images -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.etale_le_ph :
  ∀ {S : Scheme.{u}},
    (etaleTopology : GrothendieckTopology (AlgebraicSpace S)) ≤ phTopology S)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.phOver_hasSheafify_addCommGrp :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    HasSheafify (bigPhSite X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.phOver_hasInjectiveResolutions :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    HasInjectiveResolutions (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilonPullback :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilonPullback_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilonPullback X =
      comparisonTopologyPullbackAb AlgebraicGeometry.AlgebraicSpace.PhComparison.etale_le_ph X)

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aInverseImage :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (bigPhSite X) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.aInverseImage_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.PhComparison.aInverseImage X =
      etalePiInverseImage X ⋙ AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilonPullback X)

end
