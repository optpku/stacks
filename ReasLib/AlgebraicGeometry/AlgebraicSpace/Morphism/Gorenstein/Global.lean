/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian.OfScheme

/-!
# Global Gorenstein morphisms of algebraic spaces

Global Gorensteinness means locally Noetherian fibres and Gorensteinness at
every source point. The pointwise predicate itself does not require locally
Noetherian fibres.
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

/-- A morphism of algebraic spaces is Gorenstein if its fibres are locally
Noetherian and it is Gorenstein at every point of the source. -/
class Gorenstein {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends LocallyNoetherianFibers f where
  /-- A Gorenstein morphism is Gorenstein at every source point. -/
  gorensteinAt_forall : ∀ x : Points X, GorensteinAt f x

namespace Gorenstein

/-- A Gorenstein morphism of algebraic spaces is Gorenstein at every source
point. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] (x : Points X) : GorensteinAt f x :=
  Gorenstein.gorensteinAt_forall x

/-- A morphism with locally Noetherian fibres that is Gorenstein at every source
point is a Gorenstein morphism. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [LocallyNoetherianFibers f]
    (h : ∀ x : Points X, GorensteinAt f x) : Gorenstein f where
  toLocallyNoetherianFibers := inferInstance
  gorensteinAt_forall := h

/-- A morphism with locally Noetherian fibres is Gorenstein if and only if it is
Gorenstein at every source point. -/
theorem gorenstein_iff_forall_gorensteinAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f] :
    Gorenstein f ↔ ∀ x : Points X, GorensteinAt f x :=
  ⟨fun h ↦ h.gorensteinAt_forall, of⟩

/-- Without a fibre hypothesis, global Gorensteinness includes both locally
Noetherian fibres and the pointwise condition. -/
theorem gorenstein_iff_locallyNoetherianFibers_and_forall_gorensteinAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Gorenstein f ↔ LocallyNoetherianFibers f ∧ ∀ x : Points X, GorensteinAt f x := by
  constructor
  · intro hg
    exact ⟨hg.toLocallyNoetherianFibers, hg.gorensteinAt_forall⟩
  · rintro ⟨hN, hg⟩
    exact { toLocallyNoetherianFibers := hN, gorensteinAt_forall := hg }

/-- A Gorenstein morphism of algebraic spaces is flat. -/
instance instFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] : Flat f :=
  (flat_iff_forall_flatAt f).mpr fun x ↦ (spec f x).flatAt

end Gorenstein

/-- Global Gorensteinness agrees for a scheme morphism and its associated
morphism of algebraic spaces, including the locally Noetherian fibre condition. -/
theorem gorenstein_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Gorenstein (ofOverMap h) ↔ AlgebraicGeometry.Gorenstein h.left := by
  constructor
  · intro hg
    haveI : ∀ v : V.left, AlgebraicGeometry.IsLocallyNoetherian (h.left.fiber v) :=
      (locallyNoetherianFibers_ofOverMap_iff h).mp hg.toLocallyNoetherianFibers
    exact AlgebraicGeometry.Gorenstein.of_forall_gorensteinAt h.left fun u ↦
      (gorensteinAt_ofOverMap_iff h u).mp (hg.gorensteinAt_forall _)
  · intro hg
    letI := hg
    haveI : ∀ v : V.left, AlgebraicGeometry.IsLocallyNoetherian (h.left.fiber v) :=
      fun v ↦ inferInstance
    apply Gorenstein.of
    intro x
    obtain ⟨u, rfl⟩ := (ofOver.pointsEquiv U).surjective x
    exact (gorensteinAt_ofOverMap_iff h u).mpr
      (AlgebraicGeometry.Gorenstein.atPoint h.left u)

/-- A morphism of schemes over `S` that is Gorenstein remains Gorenstein after
viewing it as a morphism of algebraic spaces. -/
instance instGorenstein_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Gorenstein h.left] : Gorenstein (ofOverMap h) :=
  (gorenstein_ofOverMap_iff h).mpr inferInstance

end AlgebraicGeometry.AlgebraicSpace
