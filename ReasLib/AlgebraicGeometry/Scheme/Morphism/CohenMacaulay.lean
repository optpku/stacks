/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Cohen--Macaulay morphisms of schemes

This file defines Cohen--Macaulayness at a point of a scheme morphism and the
corresponding global morphism property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A scheme morphism is Cohen--Macaulay at `x` when it is flat at `x` and the
local ring of the fibre at the distinguished point is Cohen--Macaulay. -/
def CohenMacaulayAt (f : X ⟶ Y) (x : X) : Prop :=
  f.flatAt x ∧ CohenMacaulayRing (fiberStalkAt f x)

/-- A scheme morphism is Cohen--Macaulay at a point exactly when it is flat
there and its distinguished fibre stalk is a Cohen--Macaulay ring. -/
theorem cohenMacaulayAt_iff (f : X ⟶ Y) (x : X) :
    f.CohenMacaulayAt x ↔
      f.flatAt x ∧ CohenMacaulayRing (fiberStalkAt f x) := Iff.rfl

namespace CohenMacaulayAt

/-- A morphism that is Cohen--Macaulay at a point is flat there. -/
theorem flatAt {f : X ⟶ Y} {x : X} (h : f.CohenMacaulayAt x) :
    f.flatAt x := h.1

/-- The distinguished fibre stalk of a morphism that is Cohen--Macaulay at a
point is a Cohen--Macaulay ring. -/
theorem fiberStalk {f : X ⟶ Y} {x : X} (h : f.CohenMacaulayAt x) :
    CohenMacaulayRing (fiberStalkAt f x) := h.2

end CohenMacaulayAt

end Scheme.Hom

/-- A scheme morphism is Cohen--Macaulay when it is Cohen--Macaulay at every
point of its source. -/
class CohenMacaulay {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  pointwise : ∀ x : X, f.CohenMacaulayAt x

/-- The morphism property of being Cohen--Macaulay. -/
abbrev cohenMacaulayProperty : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ CohenMacaulay f

namespace CohenMacaulay

variable {X Y : Scheme.{u}}

/-- Every Cohen--Macaulay scheme morphism is flat. -/
instance instFlat (f : X ⟶ Y) [CohenMacaulay f] : Flat f :=
  (Scheme.Hom.flat_iff_forall_flatAt f).2 fun x ↦ (CohenMacaulay.pointwise x).1

/-- Every locally Noetherian fibre of a Cohen--Macaulay scheme morphism is a
Cohen--Macaulay scheme. -/
instance instFiber (f : X ⟶ Y) [CohenMacaulay f]
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)] (y : Y) :
    Scheme.CohenMacaulay (f.fiber y) := by
  apply ((Scheme.cohenMacaulay_tfae_stalk_and_closedPointStalk (f.fiber y)).out 0 1).mpr
  refine ⟨inferInstance, fun z ↦ ?_⟩
  have aux : ∀ (x : X) (y : Y) (z : f.fiber y),
      f x = y → f.fiberι y z = x →
        CohenMacaulayRing ((f.fiber y).presheaf.stalk z) := by
    intro x y z hy hz
    subst y
    have hz₁ : f.asFiber x = z :=
      (f.fiberι (f x)).isEmbedding.injective (by simpa using hz.symm)
    subst z
    exact (CohenMacaulay.pointwise x).2
  apply aux (f.fiberι y z) y z
  · have hz : f.fiberι y z ∈ Set.range (f.fiberι y) := ⟨z, rfl⟩
    simpa only [Scheme.Hom.range_fiberι, Set.mem_preimage, Set.mem_singleton_iff] using hz
  · rfl

end CohenMacaulay

/-- A scheme morphism is Cohen--Macaulay exactly when it is Cohen--Macaulay at
every point of its source. -/
theorem cohenMacaulay_iff_forall_cohenMacaulayAt {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    CohenMacaulay f ↔ ∀ x : X, f.CohenMacaulayAt x :=
  ⟨fun h ↦ @CohenMacaulay.pointwise _ _ _ h, fun h ↦ ⟨h⟩⟩

/-- A scheme morphism with locally Noetherian fibres is Cohen--Macaulay exactly
when it is flat and all of its fibres are Cohen--Macaulay schemes. -/
theorem cohenMacaulay_iff_flat_and_fibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) [∀ y : Y, IsLocallyNoetherian (f.fiber y)] :
    CohenMacaulay f ↔
      Flat f ∧ ∀ y : Y, Scheme.CohenMacaulay (f.fiber y) := by
  constructor
  · intro h
    letI : CohenMacaulay f := h
    exact ⟨inferInstance, fun y ↦ inferInstance⟩
  · rintro ⟨hf, hfib⟩
    refine ⟨fun x ↦ ⟨(Scheme.Hom.flat_iff_forall_flatAt f).1 hf x, ?_⟩⟩
    have hstalk : IsLocallyNoetherian (f.fiber (f x)) ∧
        ∀ z : f.fiber (f x), CohenMacaulayRing ((f.fiber (f x)).presheaf.stalk z) :=
      ((Scheme.cohenMacaulay_tfae_stalk_and_closedPointStalk (f.fiber (f x))).out 0 1).mp
        (hfib (f x))
    exact hstalk.2 (f.asFiber x)

end AlgebraicGeometry
