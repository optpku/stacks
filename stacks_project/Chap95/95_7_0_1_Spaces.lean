/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import stacks_project.Chap66.Definition_66_18_1_Site
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces

/-!
# The category of algebraic spaces over schemes

An object of `Spaces` over a scheme `S` is a morphism `X ⟶ ofOver U` of algebraic
spaces over `S`, with `U` a scheme over `S`. Morphisms are commutative squares.
-/
