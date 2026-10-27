/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleLowerShriek
import StacksCheckRecall

/-!
# Lower shriek of restricted structure sheaves

On an algebraic stack, module lower shriek of the restricted structure sheaf
along the lisse-étale and flat-fppf inclusions recovers `𝒪_X`. The
identification is the canonical `𝒪`-module adjunct of `𝒪' = g⁻¹ 𝒪`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 103.14.5 (1): module lower shriek of the lisse-étale structure sheaf
is the étale structure sheaf via the canonical comparison. -/
@[stacks 078A] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.structureSheafComparison_isIso :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsIso (SheafOfModules.pullbackObjUnitToUnit (F := lisseEtaleInclusion X)
        (𝟙 (lisseEtaleStructureSheaf X) :
          lisseEtaleStructureSheaf X ⟶
            ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
              (lisseEtaleTopology X) X.etaleTopology).obj (etaleStructureSheaf X))))

/- Lemma 103.14.5 (2): module lower shriek of the flat-fppf structure sheaf
is the fppf structure sheaf via the canonical comparison. -/
@[stacks 078A] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.structureSheafComparison_isIso :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsIso (SheafOfModules.pullbackObjUnitToUnit (F := flatFppfInclusion X)
        (𝟙 (flatFppfStructureSheaf X) :
          flatFppfStructureSheaf X ⟶
            ((flatFppfInclusion X).sheafPushforwardContinuous RingCat.{u}
              (flatFppfTopology X) (inheritedFppfTopology X)).obj (structureSheaf X))))
