/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction

/-!
# Separation properties of finite group action relations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The relation map of a finite residue-field free group action on a quasi-separated
scheme over the base is quasi-compact. -/
instance instQuasiCompact_hom_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [QuasiSeparated U.hom] : QuasiCompact (ofAut ρ).hom.left := sorry

/-- The relation map of a finite residue-field free group action on a separated scheme
over the base is a closed immersion. -/
instance instIsClosedImmersion_hom_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u}
    [Group G] [Finite G] (ρ : G →* Aut U) [IsResidueFieldFree ρ]
    [IsSeparated U.hom] : IsClosedImmersion (ofAut ρ).hom.left := sorry

end AlgebraicGeometry.Scheme.PreRelation
