/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Domination
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Section

/-!
# Extension of sections of proper morphisms

This module records when a section of a proper morphism over an open subscheme extends after an
admissible blowup of the ambient scheme.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A section of a proper morphism over a quasi-compact open extends over the inverse image of a
larger quasi-compact open after an admissible blowup of the ambient quasi-compact,
quasi-separated scheme. -/
theorem exists_isAdmissibleBlowup_extending_section
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (U W : S.Opens) (hUW : U ≤ W) [QuasiCompact U.ι] [QuasiCompact W.ι]
    (f : X ⟶ W.toScheme) [IsProper f]
    (s : U.toScheme ⟶ X) (hs : s ≫ f = S.homOfLE hUW) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (s' : (b ⁻¹ᵁ W).toScheme ⟶ X),
      IsAdmissibleBlowup U b ∧
        (b ∣_ U) ≫ s = S'.homOfLE (b.preimage_mono hUW) ≫ s' ∧
          s' ≫ f = b ∣_ W := sorry

end AlgebraicGeometry
