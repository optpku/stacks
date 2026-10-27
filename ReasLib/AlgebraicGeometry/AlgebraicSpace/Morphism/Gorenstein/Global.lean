/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.Gorenstein

/-!
# Global Gorenstein morphisms of algebraic spaces

Global Gorensteinness means Gorensteinness at every source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty
open Scheme.Germ.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Pointwise Gorensteinness is flatness at the point together with the existence
of an étale scheme square through that point with Gorenstein fibre stalk. -/
theorem gorensteinAt_iff_flat_and_existsEtaleSquareAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    GorensteinAt f x ↔
      FlatAt f x ∧ existsEtaleSquareAt fiberStalkGorenstein f x :=
  sorry

/-- Pointwise Gorensteinness is equivalent to flatness at the point together with
the fibre-stalk Gorenstein property on every étale scheme square through that
point. -/
theorem gorensteinAt_iff_forallEtaleSquareAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    GorensteinAt f x ↔
      FlatAt f x ∧ forallEtaleSquareAt fiberStalkGorenstein f x :=
  sorry

/-- A morphism of algebraic spaces is Gorenstein if it is Gorenstein at every
point of the source. -/
class Gorenstein {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- A Gorenstein morphism is Gorenstein at every source point. -/
  gorensteinAt_forall : ∀ x : Points X, GorensteinAt f x

namespace Gorenstein

/-- A Gorenstein morphism of algebraic spaces is Gorenstein at every source
point. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] (x : Points X) : GorensteinAt f x :=
  Gorenstein.gorensteinAt_forall x

/-- A morphism of algebraic spaces that is Gorenstein at every source point is a
Gorenstein morphism. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ x : Points X, GorensteinAt f x) : Gorenstein f :=
  ⟨h⟩

/-- A morphism of algebraic spaces is Gorenstein if and only if it is Gorenstein
at every source point. -/
theorem gorenstein_iff_forall_gorensteinAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Gorenstein f ↔ ∀ x : Points X, GorensteinAt f x :=
  ⟨fun h ↦ h.gorensteinAt_forall, fun h ↦ ⟨h⟩⟩

/-- A Gorenstein morphism of algebraic spaces is flat. -/
instance instFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] : Flat f :=
  (flat_iff_forall_flatAt f).mpr fun x ↦ (spec f x).flatAt

end Gorenstein

/-- A morphism of schemes over `S` that is Gorenstein remains Gorenstein after
viewing it as a morphism of algebraic spaces. -/
instance instGorenstein_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Gorenstein h.left] : Gorenstein (ofOverMap h) where
  gorensteinAt_forall := by
    intro x
    obtain ⟨u, rfl⟩ := (ofOver.pointsEquiv U).surjective x
    exact (gorensteinAt_ofOverMap_iff h u).mpr (AlgebraicGeometry.Gorenstein.atPoint h.left u)

end AlgebraicGeometry.AlgebraicSpace
