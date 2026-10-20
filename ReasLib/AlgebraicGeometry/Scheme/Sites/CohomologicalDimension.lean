/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.HigherDirectImage

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A bound for the cohomological dimension of a quasi-compact and quasi-separated scheme
morphism, expressed by vanishing of all higher direct images of locally torsion abelian sheaves
on the small étale site. -/
def cohomologicalDimensionBound (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (n : WithTop ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] : Prop :=
  ∀ (i : ℕ), n < (i : WithTop ℕ) →
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      Sheaf.IsLocallyTorsion F →
        IsZero (Sheaf.higherDirectImage (Scheme.smallEtalePullback f) F i :
          Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

/-- The cohomological dimension of a quasi-compact and quasi-separated scheme morphism is
the infimum of the bounds above which all higher direct images of locally torsion abelian
sheaves on its small étale site vanish. -/
def cohomologicalDimension (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] : WithTop ℕ :=
  sInf {n : WithTop ℕ | cohomologicalDimensionBound f n}

/-- The cohomological dimension itself satisfies the defining higher-direct-image vanishing
condition. -/
theorem cohomologicalDimension_isBound (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    cohomologicalDimensionBound f (cohomologicalDimension f) := sorry

/-- Every admissible higher-direct-image bound is above the cohomological dimension. -/
theorem cohomologicalDimension_le_of_bound (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (n : WithTop ℕ) (hn : cohomologicalDimensionBound f n) :
    cohomologicalDimension f ≤ n := sorry

end AlgebraicGeometry.Scheme.Hom

end
