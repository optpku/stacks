/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Flat groupoids in algebraic spaces

Groupoid inversion identifies flatness of the source and target maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces is flat when its source map is
flat; equivalently, both its source and target maps are flat. -/
abbrev Flat {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Prop :=
  AlgebraicSpace.Flat G.s.left

namespace Flat

/-- For a groupoid in algebraic spaces, flatness of the source map is
equivalent to flatness of the target map. -/
theorem source_iff_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Flat G.s.left ↔
      AlgebraicSpace.Flat G.t.left := sorry

/-- The source map of a flat groupoid is flat. -/
theorem source {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (h : Flat G) :
    AlgebraicSpace.Flat G.s.left := sorry

/-- The target map of a flat groupoid is flat. -/
theorem target {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (h : Flat G) :
    AlgebraicSpace.Flat G.t.left := sorry

/-- The discrete groupoid on an algebraic space over `B` is flat. -/
theorem discrete {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    Flat (GroupoidAlgebraicSpace.discrete U) := sorry

/-- A groupoid in algebraic spaces is flat if its source and target
maps are flat. -/
theorem of {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (hs : AlgebraicSpace.Flat G.s.left)
    (ht : AlgebraicSpace.Flat G.t.left) :
    Flat G := sorry

/-- A groupoid in algebraic spaces is flat if and only if its source
and target maps are flat. -/
theorem iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Flat G ↔
      AlgebraicSpace.Flat G.s.left ∧
        AlgebraicSpace.Flat G.t.left := sorry

end Flat

end AlgebraicGeometry.GroupoidAlgebraicSpace
