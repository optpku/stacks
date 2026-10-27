/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift

/-!
# Flat lifts of an `𝒪_X`-module along a morphism of first-order thickenings

A flat lift of an `𝒪_X`-module `F` along `(f, f')` is an `𝒪_{X'}`-module `F'` which is
flat over `S'` and restricts to `F` along `i`.

The canonical definition, constructor, and specification live in
`ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift`. This module re-exports
that API for the obstruction theory of morphisms of thickenings.
-/
