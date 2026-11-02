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
    (genericPoints.ofComponent Z : X) ∈ f.domain := by
  let U : Set X := (⋃₀ (irreducibleComponents X \ {Z.1}))ᶜ
  have hfinite : (irreducibleComponents X).Finite := Set.toFinite _
  have hU : IsOpen U := by
    dsimp only [U]
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfinite.sdiff.isClosed_biUnion fun W hW ↦
      isClosed_of_mem_irreducibleComponents W hW.1
  have hclosure : closure U = Z.1 :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfinite Z.1 Z.2
  have hne : U.Nonempty := by
    rw [← closure_nonempty_iff, hclosure]
    exact Z.2.1.nonempty
  obtain ⟨x, hxU, hxf⟩ := f.dense_domain.inter_open_nonempty U hU hne
  have hxZ : x ∈ Z.1 := hclosure ▸ (subset_closure hxU)
  exact ((genericPoints.isGenericPoint_ofComponent Z).specializes hxZ).mem_open
    f.domain.2 hxf

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
    f.fromSpecStalkOfComponent Z = g.fromSpecStalkOfComponent Z := by
  obtain ⟨W, hW, hWf, hWg, e⟩ := h
  have hx := (f.restrict W hW hWf).genericPointOfComponent_mem_domain Z
  dsimp only [fromSpecStalkOfComponent]
  rw [← f.fromSpecStalkOfMem_restrict hW hWf hx,
    ← g.fromSpecStalkOfMem_restrict hW hWg hx]
  exact congrArg (fun k : W.toScheme ⟶ Y ↦ W.fromSpecStalkOfMem _ hx ≫ k) e

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
    f.toRationalMap.fromSpecStalkOfComponent Z = f.fromSpecStalkOfComponent Z :=
  rfl

/-- Evaluation of a rational map over `S` at a component generic point commutes with the
structure maps to `S`. -/
theorem fromSpecStalkOfComponent_isOver {S X Y : Scheme.{u}}
    [X.Over S] [Y.Over S] [Finite (irreducibleComponents X)]
    (f : X ⤏ Y) (hf : f.IsOver S) (Z : irreducibleComponents X) :
    f.fromSpecStalkOfComponent Z ≫ Y ↘ S =
      X.fromSpecStalk (genericPoints.ofComponent Z) ≫ X ↘ S := by
  obtain ⟨p, hp, rfl⟩ := hf.exists_partialMap_over
  have hp' := PartialMap.isOver_iff.mp hp
  change p.hom ≫ Y ↘ S = p.domain.ι ≫ X ↘ S at hp'
  rw [fromSpecStalkOfComponent_toRationalMap]
  dsimp only [PartialMap.fromSpecStalkOfComponent, PartialMap.fromSpecStalkOfMem]
  rw [Category.assoc, hp', ← Category.assoc,
    Opens.fromSpecStalkOfMem_ι]

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
    (componentStalkMap S X Y f Z).1 = f.1.fromSpecStalkOfComponent Z :=
  rfl

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
