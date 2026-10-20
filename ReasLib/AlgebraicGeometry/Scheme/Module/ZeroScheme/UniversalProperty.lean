/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme

/-!
# Universal property of zero schemes

This file relates vanishing of a pulled-back section to containment of the section's zero ideal
sheaf and to factorization through its zero scheme.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- Pullback of a section vanishes exactly when its zero ideal sheaf is contained in the kernel
ideal sheaf of the morphism. -/
theorem pullbackSections_eq_zero_iff_zeroIdealSheaf_le_ker
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (f : Y ⟶ X) :
    Scheme.Modules.sectionsPullback f ℒ s =
        (0 : ((Scheme.Modules.pullback f).obj ℒ).sections) ↔
      zeroIdealSheaf ℒ s ≤ Scheme.Hom.ker f := sorry

/-- Pullback of a section vanishes exactly when the morphism factors through the section's zero
scheme. -/
theorem pullbackSections_eq_zero_iff_exists_factorization_zeroScheme
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (f : Y ⟶ X) :
    Scheme.Modules.sectionsPullback f ℒ s =
        (0 : ((Scheme.Modules.pullback f).obj ℒ).sections) ↔
      ∃ g : Y ⟶ zeroScheme ℒ s, g ≫ zeroSchemeι ℒ s = f := sorry

/-- Every morphism on which a section vanishes factors through the section's zero scheme. -/
theorem exists_factorization_zeroScheme_of_pullbackSections_eq_zero
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (i : Z ⟶ X)
    (hzero : Scheme.Modules.sectionsPullback i ℒ s =
      (0 : ((Scheme.Modules.pullback i).obj ℒ).sections)) :
    ∃ g : Z ⟶ zeroScheme ℒ s, g ≫ zeroSchemeι ℒ s = i := sorry

end AlgebraicGeometry.Scheme
