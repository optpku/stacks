/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleSite.AffineComparison
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap87.Lemma_87_19_13_Over
public import stacks_project.Chap87.Lemma_87_34_6_Comparison

/-! # Class-based compatibility for the affine étale comparison

These four specializations retain the legacy reduction interface for existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [RX : Reduction X]

/-- Reduction pullback on affine formal étale domains, specialized to the active reduction. -/
def toAffineEtale : AffineEtaleOver X ⥤ AlgebraicSpace.affineEtaleSite (reduction X) :=
  ReductionData.toAffineEtale RX.toReductionData

/-- Extension of affine étale charts, specialized to the active reduction. -/
def ofAffineEtale : AlgebraicSpace.affineEtaleSite (reduction X) ⥤ AffineEtaleOver X :=
  ReductionData.ofAffineEtale RX.toReductionData

/-- The affine étale unit, specialized to the active reduction. -/
def affineEtaleUnitIso : 𝟭 (AffineEtaleOver X) ≅ toAffineEtale ⋙ ofAffineEtale :=
  ReductionData.affineEtaleUnitIso RX.toReductionData

/-- The affine étale counit, specialized to the active reduction. -/
def affineEtaleCounitIso :
    ofAffineEtale ⋙ toAffineEtale ≅ 𝟭 (AlgebraicSpace.affineEtaleSite (reduction X)) :=
  ReductionData.affineEtaleCounitIso RX.toReductionData

end AlgebraicGeometry.FormalAlgebraicSpace
