/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowMotive.ProjectiveLine

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped CategoryTheory.MonoidalCategory
open ChowMotive.ProjectiveLine

universe u

/- Remark 45.4.5 (Lefschetz and Tate motive)
For X = ℙ¹_k and the projector c₂ of Example 45.3.7, the Lefschetz motive
(X, c₂, 0) is isomorphic to the point Tate twist 𝟙(-1) by Lemma 45.4.4,
hence tensor-invertible in Chow motives with inverse the Tate motive 𝟙(1).
Literature names L, ℒ, Q(-1), h²(ℙ¹_k) and L⁻¹, ℒ⁻¹, T, Q(1) are nomenclature only. -/
@[stacks 0FGE] #check (ChowMotive.ProjectiveLine.instIsInvertibleObjectTateProjectorMotive :
  ∀ {k : Type u} [Field k]
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1),
      MonoidalCategory.isInvertibleObject
        (ChowMotive.ProjectiveLine.tateProjectorMotive x))

#check (ChowMotive.ProjectiveLine.tateProjectorIsoTwist :
  ∀ {k : Type u} [Field k]
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1),
    ChowMotive.ProjectiveLine.tateProjectorMotive x ≅
      ChowMotive.tateTwist (SchemeOverField.point k) (-1))

#check (ChowMotive.ProjectiveLine.lefschetzTensorTateIso :
  ∀ {k : Type u} [Field k]
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1),
    ChowMotive.ProjectiveLine.tateProjectorMotive x ⊗
        ChowMotive.tateTwist (SchemeOverField.point k) 1 ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)))

#check (ChowMotive.ProjectiveLine.tateTensorLefschetzIso :
  ∀ {k : Type u} [Field k]
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1),
    ChowMotive.tateTwist (SchemeOverField.point k) 1 ⊗
        ChowMotive.ProjectiveLine.tateProjectorMotive x ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)))
