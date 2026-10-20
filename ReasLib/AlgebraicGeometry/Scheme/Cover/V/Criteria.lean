/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Covering
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import ReasLib.AlgebraicGeometry.Scheme.Topology.Valuation

/-!
# Criteria for singleton valuative coverings

This module characterizes singleton `V` coverings using valuation-ring lifts
and specialization lifts after arbitrary base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A scheme morphism has the valuation-ring extension lifting property when every
valuation-ring point of its target lifts after an extension of valuation rings. -/
def ValuationRingExtensionLift {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃V : Type u⦄ [CommRing V] [IsDomain V] [ValuationRing V]
    (g : Spec (CommRingCat.of V) ⟶ Y),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (_ : Algebra V W) (_ : IsExtensionOfValuationRings V W)
        (lift : Spec (CommRingCat.of W) ⟶ X),
          Spec.map (CommRingCat.ofHom (algebraMap V W)) ≫ g = lift ≫ f

/-- A scheme morphism has the universal specialization lifting property when every
specialization in every base scheme lifts to a specialization in the corresponding pullback. -/
def UniversalSpecializationLift {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃Z : Scheme.{u}⦄ (g : Z ⟶ Y) ⦃z' z : Z⦄, z' ⤳ z →
    ∃ (w' w : (pullback f g : Scheme.{u})),
      w' ⤳ w ∧ (pullback.snd f g w', pullback.snd f g w) = (z', z)

/-- For a quasi-compact scheme morphism, being a singleton `V` covering, lifting
valuation-ring points after extension, and universally lifting specializations are equivalent. -/
@[stacks 0ETN]
theorem isVCovering_singleton_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    List.TFAE [
      IsVCovering Y (fun _ : PUnit ↦ X) (fun _ ↦ f),
      ValuationRingExtensionLift f,
      UniversalSpecializationLift f] := sorry

/-- A quasi-compact scheme morphism is a singleton `V` covering exactly when every
valuation-ring point of its target lifts after an extension of valuation rings. -/
theorem isVCovering_singleton_iff_valuationRingExtensionLift
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsVCovering Y (fun _ : PUnit ↦ X) (fun _ ↦ f) ↔ ValuationRingExtensionLift f := sorry

/-- A quasi-compact scheme morphism is a singleton `V` covering exactly when every
specialization lifts after arbitrary base change. -/
theorem isVCovering_singleton_iff_universalSpecializationLift
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsVCovering Y (fun _ : PUnit ↦ X) (fun _ ↦ f) ↔ UniversalSpecializationLift f := sorry

end AlgebraicGeometry
