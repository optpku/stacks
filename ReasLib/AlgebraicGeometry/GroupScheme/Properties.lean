/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- A group scheme is smooth when its structure morphism is smooth. -/
abbrev Smooth {S : Scheme.{u}} (G : Grp (Over S)) : Prop :=
  AlgebraicGeometry.Smooth G.X.hom

/-- A group scheme is flat when its structure morphism is flat. -/
abbrev Flat {S : Scheme.{u}} (G : Grp (Over S)) : Prop :=
  AlgebraicGeometry.Flat G.X.hom

/-- A group scheme is separated when its structure morphism is separated. -/
abbrev IsSeparated {S : Scheme.{u}} (G : Grp (Over S)) : Prop :=
  AlgebraicGeometry.IsSeparated G.X.hom

end AlgebraicGeometry.GroupScheme
