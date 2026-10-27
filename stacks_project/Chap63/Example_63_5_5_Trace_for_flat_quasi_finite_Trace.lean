/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.FiberWeight

/-!
# Canonical sheaf traces for flat locally quasi-finite morphisms

The canonical sheaf trace is the trace for the positive fibre-weight weighting.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Etale

universe u

#check (AlgebraicGeometry.Scheme.Etale.fiberWeightTraceHom :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F)
