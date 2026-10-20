/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism between schemes of finite type over a field has finite relative étale
cohomological dimension. -/
theorem Hom.cohomologicalDimension_ne_top
    {K : Type u} [Field K] {X Y : SchemeOverField K} [Algebraic X] [Algebraic Y]
    (f : X ⟶ Y)
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})] :
    Hom.cohomologicalDimension f.left ≠ ⊤ := sorry

/-- A scheme of finite type over a field of finite étale cohomological dimension has finite
étale cohomological dimension. -/
theorem cohomologicalDimension_ne_top
    {K : Type u} [Field K] {X : SchemeOverField K} [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
    (hK : cohomologicalDimension (Spec (CommRingCat.of K)) ≠ ⊤) :
    cohomologicalDimension X.left ≠ ⊤ := sorry

end AlgebraicGeometry.Scheme

end
