/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.RepresentedSections

/-! # Compatible sections of represented direct images -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open scoped Bicategory
universe u

#check (AlgebraicGeometry.GroupoidsOver.hasSmallCFGTypeSections_ofRepresented :
  ∀ {S : Scheme.{u}} {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S}
    (eU : U.toGroupoids ≌ Ucfg) (eV : V.toGroupoids ≌ Vcfg),
    GroupoidsOver.HasSmallCFGTypeSections (S := S) a)

#check (AlgebraicGeometry.GroupoidsOver.moduleComparisonSpaceMorphism :
  ∀ {S : Scheme.{u}} {Ucfg Vcfg : GroupoidsOver S}
    (a : Ucfg ⟶ Vcfg) {U V : AlgebraicSpace S},
    (U.toGroupoids ≌ Ucfg) → (V.toGroupoids ≌ Vcfg) → (U ⟶ V))
