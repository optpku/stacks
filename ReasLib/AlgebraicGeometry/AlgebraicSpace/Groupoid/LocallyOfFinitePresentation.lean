/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Locally finitely presented groupoids in algebraic spaces

Groupoid inversion identifies local finite presentation of the source and target maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces is locally of finite presentation when its source map is
locally of finite presentation; equivalently, both its source and target maps are locally of finite presentation. -/
abbrev LocallyOfFinitePresentation {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Prop :=
  AlgebraicSpace.LocallyOfFinitePresentation G.s.left

namespace LocallyOfFinitePresentation

/-- For a groupoid in algebraic spaces, local finite presentation of the source map is
equivalent to local finite presentation of the target map. -/
theorem source_iff_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.LocallyOfFinitePresentation G.s.left ↔
      AlgebraicSpace.LocallyOfFinitePresentation G.t.left := sorry

/-- The source map of a locally of finite presentation groupoid is locally of finite presentation. -/
theorem source {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (h : LocallyOfFinitePresentation G) :
    AlgebraicSpace.LocallyOfFinitePresentation G.s.left := sorry

/-- The target map of a locally of finite presentation groupoid is locally of finite presentation. -/
theorem target {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (h : LocallyOfFinitePresentation G) :
    AlgebraicSpace.LocallyOfFinitePresentation G.t.left := sorry

/-- The discrete groupoid on an algebraic space over `B` is locally of finite presentation. -/
theorem discrete {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    LocallyOfFinitePresentation (GroupoidAlgebraicSpace.discrete U) := sorry

/-- A groupoid in algebraic spaces is locally of finite presentation if its source and target
maps are locally of finite presentation. -/
theorem of {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (hs : AlgebraicSpace.LocallyOfFinitePresentation G.s.left)
    (ht : AlgebraicSpace.LocallyOfFinitePresentation G.t.left) :
    LocallyOfFinitePresentation G := sorry

/-- A groupoid in algebraic spaces is locally of finite presentation if and only if its source
and target maps are locally of finite presentation. -/
theorem iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    LocallyOfFinitePresentation G ↔
      AlgebraicSpace.LocallyOfFinitePresentation G.s.left ∧
        AlgebraicSpace.LocallyOfFinitePresentation G.t.left := sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.GroupoidAlgebraicSpace
