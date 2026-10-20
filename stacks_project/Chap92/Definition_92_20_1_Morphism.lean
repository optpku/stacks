/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent

/-!
# Cotangent complexes of morphisms of ringed spaces

This leaf provides the source-facing compatibility surface for the cotangent complexes of
morphisms of ringed spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

#check (AlgebraicGeometry.RingedSpace.cotangentComplex :
  ∀ {X S : AlgebraicGeometry.RingedSpace.{u}},
    (X ⟶ S) → CochainComplex X.Modules ℤ)
