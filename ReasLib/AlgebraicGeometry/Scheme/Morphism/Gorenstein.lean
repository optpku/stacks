/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Gorenstein morphisms of schemes

This file defines Gorensteinness at a point of a scheme morphism and the
corresponding global morphism property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A scheme morphism is Gorenstein at `x` when it is flat at `x` and the local
ring of the fibre at the distinguished point is Gorenstein. -/
def gorensteinAt (f : X ⟶ Y) (x : X) : Prop :=
  f.flatAt x ∧ IsGorensteinLocalRing (fiberStalkAt f x)

/-- Pointwise Gorensteinness is equivalent to pointwise flatness together with
Gorensteinness of the local ring of the fibre at the distinguished point. -/
theorem gorensteinAt_iff (f : X ⟶ Y) (x : X) :
    f.gorensteinAt x ↔
      f.flatAt x ∧ IsGorensteinLocalRing (fiberStalkAt f x) := sorry

end Scheme.Hom

/-- A scheme morphism is Gorenstein when it is flat and every fibre is a
Gorenstein scheme. -/
class Gorenstein {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop extends Flat f where
  /-- Every fibre of a Gorenstein morphism is a Gorenstein scheme. -/
  fiberGorenstein (y : Y) : Scheme.Gorenstein (f.fiber y)

/-- The morphism property of being Gorenstein. -/
abbrev gorensteinProperty : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ Gorenstein f

namespace Gorenstein

variable {X Y : Scheme.{u}}

/-- Every Gorenstein scheme morphism is flat. -/
instance instFlat (f : X ⟶ Y) [h : Gorenstein f] : Flat f := h.toFlat

/-- Every fibre of a Gorenstein scheme morphism is a Gorenstein scheme. -/
instance instFiber (f : X ⟶ Y) [h : Gorenstein f] (y : Y) :
    Scheme.Gorenstein (f.fiber y) := h.fiberGorenstein y

/-- A Gorenstein scheme morphism is Gorenstein at every source point. -/
theorem atPoint (f : X ⟶ Y) [Gorenstein f] (x : X) :
    f.gorensteinAt x := sorry

/-- A morphism with locally Noetherian fibres that is Gorenstein at every source
point is a Gorenstein morphism. -/
theorem of_forall_gorensteinAt (f : X ⟶ Y)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    (h : ∀ x : X, f.gorensteinAt x) : Gorenstein f := sorry

end Gorenstein

/-- A scheme morphism is Gorenstein exactly when it is flat and all of its
fibres are Gorenstein schemes. -/
theorem gorenstein_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Gorenstein f ↔ Flat f ∧ ∀ y : Y, Scheme.Gorenstein (f.fiber y) := sorry

/-- For a morphism whose fibres are locally Noetherian, Gorensteinness is
equivalent to flatness together with Gorenstein fibres. -/
theorem gorenstein_iff_flat_and_fibers {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)] :
    Gorenstein f ↔ Flat f ∧ ∀ y : Y, Scheme.Gorenstein (f.fiber y) := gorenstein_iff f

/-- For a morphism with locally Noetherian fibres, global Gorensteinness is
equivalent to Gorensteinness at every source point. -/
theorem gorenstein_iff_forall_gorensteinAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)] :
    Gorenstein f ↔ ∀ x : X, f.gorensteinAt x := sorry

end AlgebraicGeometry
