/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Étale morphisms of algebraic spaces are open on points

An étale morphism of algebraic spaces over a scheme induces an open map of canonical
point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- An étale morphism of algebraic spaces induces an open map on canonical point spaces. -/
theorem isOpenMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    IsOpenMap (Points.map f) := sorry

/-- The image of an open set of points under an étale morphism of algebraic spaces is open. -/
theorem isOpen_image {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    {U : Set (Points X)} (hU : IsOpen U) : IsOpen (Points.map f '' U) := sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
