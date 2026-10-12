/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Lifting
public import Mathlib.CategoryTheory.LiftingProperties.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallyEtale

/-- A formally étale morphism has the lifting property against every first-order
thickening, without affineness assumptions. -/
instance hasLiftingProperty {X S T T' : Scheme.{u}} (f : X ⟶ S) [FormallyEtale f]
    (i : T ⟶ T') [IsFirstOrderThickening i] : HasLiftingProperty i f := sorry

/-- A formally étale morphism admits exactly one lift through every first-order
thickening, without affineness assumptions on the thickened schemes. -/
theorem existsUnique_lift_firstOrder {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [FormallyEtale f] (i : T ⟶ T') [IsFirstOrderThickening i]
    (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h) :
    Nonempty (Unique sq.LiftStruct) := sorry

/-- Formal étaleness is equivalent to unique lifting through arbitrary first-order
thickenings. -/
theorem iff_existsUnique_lift_firstOrder {X S : Scheme.{u}} (f : X ⟶ S) :
    FormallyEtale f ↔
      ∀ {T T' : Scheme.{u}} (i : T ⟶ T') [IsFirstOrderThickening i]
        (g : T ⟶ X) (h : T' ⟶ S) (sq : CommSq g i f h),
        Nonempty (Unique sq.LiftStruct) := sorry

end AlgebraicGeometry.FormallyEtale
