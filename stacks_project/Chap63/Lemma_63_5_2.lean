/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.5.2: existence and uniqueness of the trace with its prescribed geometric-stalk formula. -/
@[stacks 0GKG] #check (AlgebraicGeometry.Scheme.Etale.weightingTrace_existsUnique :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    ∃! φ : (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F,
      ∀ ybar : GeometricPoint Y,
        (toSmallEtalePoint ybar).sheafFiber.map φ =
          (lowerShriekStalkIso f ybar).hom.app ((etaleAbelianSheafPullback f).obj F) ≫
            (WeightingTrace.pullbackStalkCoproductIso f ybar F).hom ≫
              WeightingTrace.stalkDesc f w ybar F)

#check (AlgebraicGeometry.Scheme.Etale.weightingTrace :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F)

#check (AlgebraicGeometry.Scheme.Etale.weightingTrace_stalk :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (ybar : GeometricPoint Y),
    (toSmallEtalePoint ybar).sheafFiber.map (weightingTrace f hw F) =
      (lowerShriekStalkIso f ybar).hom.app ((etaleAbelianSheafPullback f).obj F) ≫
        (WeightingTrace.pullbackStalkCoproductIso f ybar F).hom ≫
          WeightingTrace.stalkDesc f w ybar F)

#check (AlgebraicGeometry.Scheme.Etale.weightingTrace_unique :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (φ : (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F)
    (hφ : ∀ ybar : GeometricPoint Y,
      (toSmallEtalePoint ybar).sheafFiber.map φ =
        (lowerShriekStalkIso f ybar).hom.app ((etaleAbelianSheafPullback f).obj F) ≫
          (WeightingTrace.pullbackStalkCoproductIso f ybar F).hom ≫
            WeightingTrace.stalkDesc f w ybar F),
    φ = weightingTrace f hw F)
