/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.Over
public import ReasLib.AlgebraicGeometry.Scheme.SpreadingOut

/-!
# Rational maps on the stalks of irreducible components

This file evaluates a rational map on the local spectra at the generic points
of the irreducible components of its source.
-/

@[expose] public section

open CategoryTheory hiding Quotient
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Families of maps from the local spectra at the generic points of the irreducible
components of `X` to `Y` that commute with the structure maps to `S`. -/
abbrev ComponentStalkMaps (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] :=
  ∀ Z : irreducibleComponents X,
    { g : Spec (X.presheaf.stalk (genericPoints.ofComponent Z)) ⟶ Y //
      g ≫ Y ↘ S = X.fromSpecStalk (genericPoints.ofComponent Z) ≫ X ↘ S }

/-- Component stalk maps are precisely component-indexed morphisms from the generic local
spectra that commute with the maps to the base scheme. -/
theorem componentStalkMaps_def (S X Y : Scheme.{u}) [X.Over S] [Y.Over S] :
    ComponentStalkMaps S X Y =
      (∀ Z : irreducibleComponents X,
        { g : Spec (X.presheaf.stalk (genericPoints.ofComponent Z)) ⟶ Y //
          g ≫ Y ↘ S = X.fromSpecStalk (genericPoints.ofComponent Z) ≫ X ↘ S }) :=
  rfl

namespace PartialMap

/-- Every generic point of an irreducible component belongs to the domain of a partial map
when the source has finitely many irreducible components. -/
theorem genericPointOfComponent_mem_domain {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] (f : X.PartialMap Y)
    (Z : irreducibleComponents X) :
    (genericPoints.ofComponent Z : X) ∈ f.domain := sorry

/-- The map from the local spectrum at the generic point of a component induced by a partial
map. -/
noncomputable def fromSpecStalkOfComponent {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] (f : X.PartialMap Y)
    (Z : irreducibleComponents X) :
    Spec (X.presheaf.stalk (genericPoints.ofComponent Z)) ⟶ Y :=
  f.fromSpecStalkOfMem (f.genericPointOfComponent_mem_domain Z)

/-- Equivalent partial maps induce the same map from the local spectrum at the generic point
of each irreducible component. -/
theorem fromSpecStalkOfComponent_eq_of_equiv {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] {f g : X.PartialMap Y}
    (h : f.equiv g) (Z : irreducibleComponents X) :
    f.fromSpecStalkOfComponent Z = g.fromSpecStalkOfComponent Z := sorry

end PartialMap

namespace RationalMap

/-- The map from the local spectrum at the generic point of a component induced by a rational
map. -/
noncomputable def fromSpecStalkOfComponent {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] (f : X ⤏ Y)
    (Z : irreducibleComponents X) :
    Spec (X.presheaf.stalk (genericPoints.ofComponent Z)) ⟶ Y :=
  Quotient.lift (fun p ↦ p.fromSpecStalkOfComponent Z)
    (fun _ _ h ↦ PartialMap.fromSpecStalkOfComponent_eq_of_equiv h Z) f

/-- Evaluation of the rational map represented by a partial map agrees with evaluation of that
partial map at each component generic point. -/
theorem fromSpecStalkOfComponent_toRationalMap {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] (f : X.PartialMap Y)
    (Z : irreducibleComponents X) :
    f.toRationalMap.fromSpecStalkOfComponent Z = f.fromSpecStalkOfComponent Z := sorry

/-- Evaluation of a rational map over `S` at a component generic point commutes with the
structure maps to `S`. -/
theorem fromSpecStalkOfComponent_isOver {S X Y : Scheme.{u}}
    [X.Over S] [Y.Over S] [Finite (irreducibleComponents X)]
    (f : X ⤏ Y) (hf : f.IsOver S) (Z : irreducibleComponents X) :
    f.fromSpecStalkOfComponent Z ≫ Y ↘ S =
      X.fromSpecStalk (genericPoints.ofComponent Z) ≫ X ↘ S := sorry

/-- Evaluation of rational maps over `S` on the local spectra at the generic points of the
irreducible components of their source. -/
noncomputable def componentStalkMap (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    [Finite (irreducibleComponents X)] :
    { f : X ⤏ Y // f.IsOver S } → ComponentStalkMaps S X Y :=
  fun f Z ↦ ⟨f.1.fromSpecStalkOfComponent Z,
    f.1.fromSpecStalkOfComponent_isOver f.2 Z⟩

/-- Component-stalk evaluation has the expected value on every component. -/
theorem componentStalkMap_apply {S X Y : Scheme.{u}}
    [X.Over S] [Y.Over S] [Finite (irreducibleComponents X)]
    (f : { f : X ⤏ Y // f.IsOver S }) (Z : irreducibleComponents X) :
    (componentStalkMap S X Y f Z).1 = f.1.fromSpecStalkOfComponent Z := sorry

/-- Component-stalk evaluation of rational maps over a locally finite type target is
injective. -/
theorem componentStalkMap_injective_of_locallyOfFiniteType
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [Finite (irreducibleComponents X)] [LocallyOfFiniteType (Y ↘ S)] :
    Function.Injective (componentStalkMap S X Y) := sorry

/-- Component-stalk evaluation of rational maps over a locally finite presentation target is
bijective. -/
theorem componentStalkMap_bijective_of_locallyOfFinitePresentation
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [Finite (irreducibleComponents X)] [LocallyOfFinitePresentation (Y ↘ S)] :
    Function.Bijective (componentStalkMap S X Y) := sorry

/-- Component-stalk evaluation of rational maps from a reduced scheme to a locally finite type
target is bijective. -/
theorem componentStalkMap_bijective_of_locallyOfFiniteType_of_isReduced
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [Finite (irreducibleComponents X)] [LocallyOfFiniteType (Y ↘ S)] [IsReduced X] :
    Function.Bijective (componentStalkMap S X Y) := sorry

end RationalMap

end AlgebraicGeometry.Scheme
