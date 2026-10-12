/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- The pointwise Cohen--Macaulay predicate for scheme morphisms. -/
#check (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt :
  {X Y : Scheme.{u}} → (X ⟶ Y) → X → Prop)

/- The defining criterion for pointwise Cohen--Macaulayness. -/
#check (AlgebraicGeometry.Scheme.Hom.cohenMacaulayAt_iff :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
    f.CohenMacaulayAt x ↔
      f.flatAt x ∧ CohenMacaulayRing (Scheme.Hom.fiberStalkAt f x))

/- Pointwise Cohen--Macaulayness implies pointwise flatness. -/
#check (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.flatAt :
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X},
    f.CohenMacaulayAt x → f.flatAt x)

/- Pointwise Cohen--Macaulayness implies Cohen--Macaulayness of the
distinguished fibre stalk. -/
#check (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt.fiberStalk :
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X},
    f.CohenMacaulayAt x →
      CohenMacaulayRing (Scheme.Hom.fiberStalkAt f x))

/- The global Cohen--Macaulay predicate for scheme morphisms. -/
#check (AlgebraicGeometry.CohenMacaulay :
  {X Y : Scheme.{u}} → (X ⟶ Y) → Prop)

/- A globally Cohen--Macaulay scheme morphism is flat. -/
#check (AlgebraicGeometry.CohenMacaulay.instFlat :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [CohenMacaulay f], Flat f)

/- A locally Noetherian fibre of a globally Cohen--Macaulay morphism is a
Cohen--Macaulay scheme. -/
#check (AlgebraicGeometry.CohenMacaulay.instFiber :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [CohenMacaulay f]
      [∀ y : Y, IsLocallyNoetherian (f.fiber y)] (y : Y),
    Scheme.CohenMacaulay (f.fiber y))

/- The pointwise characterization of global Cohen--Macaulayness. -/
#check (AlgebraicGeometry.cohenMacaulay_iff_forall_cohenMacaulayAt :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    CohenMacaulay f ↔ ∀ x : X, f.CohenMacaulayAt x)

/- The flat-and-fibres characterization of global Cohen--Macaulayness. -/
#check (AlgebraicGeometry.cohenMacaulay_iff_flat_and_fibers :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [∀ y : Y, IsLocallyNoetherian (f.fiber y)],
    CohenMacaulay f ↔
      Flat f ∧ ∀ y : Y, Scheme.CohenMacaulay (f.fiber y))

end AlgebraicGeometry
