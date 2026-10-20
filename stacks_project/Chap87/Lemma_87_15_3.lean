/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Limits
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ObjectProperty
open ChosenBigFppfSite

universe u

/- Lemma 87.15.3: Let `S` be a scheme. The category of formal algebraic spaces
over `S` has fibre products. -/
@[stacks 0AJ3] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.instHasPullbacks :
    ∀ {S : Scheme.{u}}
      [HasWeakSheafify (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
      [HasPullbacks (Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))],
    HasPullbacks (ObjectProperty.FullSubcategory
      fun X : Sheaf (ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)) ↦
        AlgebraicGeometry.IsFormalAlgebraicSpace X))
