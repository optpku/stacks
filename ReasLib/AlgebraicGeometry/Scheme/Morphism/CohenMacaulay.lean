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
      f.flatAt x ∧ CohenMacaulayRing (fiberStalkAt f x) := sorry

namespace CohenMacaulayAt

/-- A morphism that is Cohen--Macaulay at a point is flat there. -/
theorem flatAt {f : X ⟶ Y} {x : X} (h : f.CohenMacaulayAt x) :
    f.flatAt x := sorry

/-- The distinguished fibre stalk of a morphism that is Cohen--Macaulay at a
point is a Cohen--Macaulay ring. -/
theorem fiberStalk {f : X ⟶ Y} {x : X} (h : f.CohenMacaulayAt x) :
    CohenMacaulayRing (fiberStalkAt f x) := sorry

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
instance instFlat (f : X ⟶ Y) [CohenMacaulay f] : Flat f := sorry

/-- Every locally Noetherian fibre of a Cohen--Macaulay scheme morphism is a
Cohen--Macaulay scheme. -/
instance instFiber (f : X ⟶ Y) [CohenMacaulay f]
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)] (y : Y) :
    Scheme.CohenMacaulay (f.fiber y) := sorry

end CohenMacaulay

/-- A scheme morphism is Cohen--Macaulay exactly when it is Cohen--Macaulay at
every point of its source. -/
theorem cohenMacaulay_iff_forall_cohenMacaulayAt {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    CohenMacaulay f ↔ ∀ x : X, f.CohenMacaulayAt x := sorry

/-- A scheme morphism with locally Noetherian fibres is Cohen--Macaulay exactly
when it is flat and all of its fibres are Cohen--Macaulay schemes. -/
theorem cohenMacaulay_iff_flat_and_fibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) [∀ y : Y, IsLocallyNoetherian (f.fiber y)] :
    CohenMacaulay f ↔
      Flat f ∧ ∀ y : Y, Scheme.CohenMacaulay (f.fiber y) := sorry

end AlgebraicGeometry
