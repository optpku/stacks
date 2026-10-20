/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Adjunction
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

noncomputable section

universe u

/- Lemma 84.5.5: for a scheme `S` and an algebraic space `X` over `S`, and for
`K` in the derived category of abelian sheaves on `X_étale`, the derived
adjunction unit `K ⟶ Rπ_{X,*} (π_X⁻¹ K)` is an isomorphism, where this unit is
`(etalePiDerivedAdjunction X).unit.app K` and `π_X` is the morphism of topoi
`Sh((Spaces/X)_étale) ⟶ Sh(X_étale)`. -/
@[stacks 0DGC] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.etalePiDerivedAdjunction_unit_isIso :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
      [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
      [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
      [Abelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
      [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
      [HasDerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
      [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
        (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
      [PreservesFiniteLimits
        ((relocalizationFunctor (𝟙 X)).op.lan :
          ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
            ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
      (K : DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
      IsIso ((etalePiDerivedAdjunction X).unit.app K))
