/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

/-!
# Smooth groupoids in algebraic spaces

Groupoid inversion identifies smoothness of the source and target maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces is smooth when its source map is smooth;
equivalently, both its source and target maps are smooth. -/
abbrev Smooth {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Prop :=
  AlgebraicSpace.Smooth G.s.left

namespace Smooth

/-- For a groupoid in algebraic spaces, smoothness of the source map is
equivalent to smoothness of the target map. -/
theorem source_iff_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Smooth G.s.left ↔ AlgebraicSpace.Smooth G.t.left := sorry

/-- The source map of a smooth groupoid is a smooth morphism of algebraic spaces. -/
theorem source {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (h : Smooth G) :
    AlgebraicSpace.Smooth G.s.left :=
  h

/-- The target map of a smooth groupoid is a smooth morphism of algebraic spaces. -/
theorem target {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (h : Smooth G) :
    AlgebraicSpace.Smooth G.t.left :=
  (source_iff_target G).mp h

/-- The discrete groupoid on an algebraic space over `B` is smooth. -/
theorem discrete {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    Smooth (GroupoidAlgebraicSpace.discrete U) := sorry

/-- A groupoid in algebraic spaces is smooth if and only if its source and
target maps are smooth morphisms of algebraic spaces. -/
theorem iff {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    Smooth G ↔ AlgebraicSpace.Smooth G.s.left ∧ AlgebraicSpace.Smooth G.t.left :=
  sorry

end Smooth

end AlgebraicGeometry.GroupoidAlgebraicSpace
