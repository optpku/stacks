/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Sheaves.Basis.Basic

/-!
# Neighborhoods from a topological basis

This file compares neighborhoods drawn from a basis with the category of all open
neighborhoods of a point.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

universe u

variable {X : TopCat.{u}}

/-- The full subcategory of basis opens containing the point `x`. -/
abbrev BasisOpenNhds (B : Set (Opens X)) (x : X) :=
  ObjectProperty.FullSubcategory fun U : BasisOpen B ↦ x ∈ U.1

/-- The inclusion of basis neighborhoods of `x` into the category of basis opens. -/
abbrev basisOpenNhdsInclusion (B : Set (Opens X)) (x : X) :
    BasisOpenNhds B x ⥤ BasisOpen B :=
  ObjectProperty.ι fun U : BasisOpen B ↦ x ∈ U.1

/-- The inclusion of basis neighborhoods of `x` into the category of all open neighborhoods of
`x`. -/
abbrev basisOpenNhdsToOpenNhds (B : Set (Opens X)) (x : X) :
    BasisOpenNhds B x ⥤ OpenNhds x where
  obj U := ⟨(basisOpenInclusion B).obj ((basisOpenNhdsInclusion B x).obj U), U.2⟩
  map {U V} i :=
    show ((basisOpenInclusion B).obj ((basisOpenNhdsInclusion B x).obj U)) ⟶
        ((basisOpenInclusion B).obj ((basisOpenNhdsInclusion B x).obj V)) from
      (basisOpenInclusion B).map ((basisOpenNhdsInclusion B x).map i)

/-- The two descriptions of the inclusion of basis neighborhoods into all open neighborhoods are
canonically naturally isomorphic. -/
public noncomputable def basisOpenNhdsInclusionIso (B : Set (Opens X)) (x : X) :
    (basisOpenNhdsInclusion B x).op ⋙ (basisOpenInclusion B).op ≅
      (basisOpenNhdsToOpenNhds B x).op ⋙ (OpenNhds.inclusion x).op :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ Subsingleton.elim _ _)

/-- Basis neighborhoods containing `x` are final among all neighborhoods of `x` when `B` is a
topological basis. -/
theorem basisOpenNhdsToOpenNhds_final {B : Set (Opens X)}
    (hB : Opens.IsBasis B) (x : X) :
    Functor.Final (basisOpenNhdsToOpenNhds B x).op := sorry

/-- The opposite of the category of basis neighborhoods of `x` is filtered when `B` is a
topological basis. -/
theorem basisOpenNhds_isFiltered {B : Set (Opens X)}
    (hB : Opens.IsBasis B) (x : X) :
    IsFiltered ((BasisOpenNhds B x)ᵒᵖ) := sorry
