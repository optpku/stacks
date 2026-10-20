/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A locally Noetherian reduced scheme is weakly normal if and only if every birational
universal homeomorphism to it admits a right section. -/
theorem weaklyNormal_iff_section_of_birational_universalHomeomorphism
    (T : Scheme.{u}) [IsLocallyNoetherian T] [IsReduced T] :
    WeaklyNormal T ↔
      ∀ {T' : Scheme.{u}} (g : T' ⟶ T) [UniversalHomeomorphism g] [IsBirational g],
        ∃ s : T ⟶ T', s ≫ g = 𝟙 T :=
  sorry

end AlgebraicGeometry.Scheme
