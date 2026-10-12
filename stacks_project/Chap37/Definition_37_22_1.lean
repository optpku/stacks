/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Definition 37.22.1 (1): Cohen--Macaulayness of a scheme morphism at a point. -/
@[stacks 045R] #check (AlgebraicGeometry.Scheme.Hom.CohenMacaulayAt :
  {X Y : Scheme.{u}} → (X ⟶ Y) → X → Prop)

/- Definition 37.22.1 (2): a Cohen--Macaulay scheme morphism is Cohen--Macaulay at every
point of its source. -/
@[stacks 045R] #check (AlgebraicGeometry.CohenMacaulay :
  {X Y : Scheme.{u}} → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Scheme.Hom.cohenMacaulayAt_iff :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
    f.CohenMacaulayAt x ↔
      f.flatAt x ∧ CohenMacaulayRing (Scheme.Hom.fiberStalkAt f x))

#check (AlgebraicGeometry.cohenMacaulay_iff_forall_cohenMacaulayAt :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    CohenMacaulay f ↔ ∀ x : X, f.CohenMacaulayAt x)

#check (AlgebraicGeometry.cohenMacaulay_iff_flat_and_fibers :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [∀ y : Y, IsLocallyNoetherian (f.fiber y)],
    CohenMacaulay f ↔
      Flat f ∧ ∀ y : Y, Scheme.CohenMacaulay (f.fiber y))

end AlgebraicGeometry
