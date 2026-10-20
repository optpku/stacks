/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Normal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a normal integral affine scheme with separably closed function field, the
first small-étale cohomology of every closed subscheme with finite constant
coefficients vanishes. -/
theorem etaleH1_constantFinite_isZero
    {X Z : Scheme.{u}} [IsAffine X] [IsIntegral X] (hX : X.isNormal)
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{u}) [Finite M]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})] :
    IsZero
      ((Sheaf.functorH Z.smallEtaleTopology 1).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M)) := sorry

/-- For a normal integral affine scheme with separably closed function field, the
positive-degree small-étale cohomology of every closed subscheme with finite
constant coefficients vanishes. -/
theorem etaleHq_constantFinite_isZero
    {X Z : Scheme.{u}} [IsAffine X] [IsIntegral X] (hX : X.isNormal)
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{u}) [Finite M]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero
      ((Sheaf.functorH Z.smallEtaleTopology q).obj
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj M)) := sorry

end AlgebraicGeometry.Scheme.Hom
