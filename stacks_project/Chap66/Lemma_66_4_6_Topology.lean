/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-! # Canonical topology of algebraic-space points

The existing public topology now also owns the original continuous/open-map laws and the
actual representable-points homeomorphism. No chapter-owned topology model remains.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Points.isOpen_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (s : Set (Points X)),
    IsOpen s ↔ ∀ ⦃U : Over S⦄ (p : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf p → IsOpen (Points.mapOfOver p ⁻¹' s))

#check (AlgebraicGeometry.AlgebraicSpace.Points.continuous_map :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Continuous (Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.Points.continuous_mapOfOver :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf p → Continuous (Points.mapOfOver p))

#check (AlgebraicGeometry.AlgebraicSpace.Points.isOpenMap_mapOfOver :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf p → IsOpenMap (Points.mapOfOver p))

#check (AlgebraicGeometry.AlgebraicSpace.ofOver.pointsHomeomorph :
  ∀ {S : Scheme.{u}} (X : Over S), X.left ≃ₜ Points (ofOver X))

end AlgebraicGeometry.AlgebraicSpace
