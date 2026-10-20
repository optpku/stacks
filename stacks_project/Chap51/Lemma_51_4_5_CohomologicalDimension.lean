/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory

universe u

/- Local-cohomological dimension bounds and their defining characterization. -/
#check (Ideal.LocalCohomology.HasDimensionLE :
  ∀ {A : Type u} [CommRing A], Ideal A → ℤ → Prop)

#check (Ideal.LocalCohomology.hasDimensionLE_iff :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (d : ℤ),
    Ideal.LocalCohomology.HasDimensionLE I d ↔
      -1 ≤ d ∧
        ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤
            DerivedCategory.IdealPowerTorsion I)
          (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ),
          (RΓ.obj (ModuleCat.single0 (ModuleCat.of A A))).obj.IsLE d)

#check (Ideal.LocalCohomology.HasDimensionLE.mono :
  ∀ {A : Type u} [CommRing A] {I : Ideal A} {d e : ℤ},
    Ideal.LocalCohomology.HasDimensionLE I d → d ≤ e →
      Ideal.LocalCohomology.HasDimensionLE I e)

#check (Ideal.LocalCohomology.exists_hasDimensionLE :
  ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
    ∃ d : ℤ, Ideal.LocalCohomology.HasDimensionLE I d)

#check (Ideal.LocalCohomology.dimension :
  ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG → ℤ)

#check (Ideal.LocalCohomology.dimension_spec :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG),
    Ideal.LocalCohomology.HasDimensionLE I (Ideal.LocalCohomology.dimension I hI))

#check (Ideal.LocalCohomology.dimension_le_iff :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ),
    Ideal.LocalCohomology.dimension I hI ≤ d ↔ Ideal.LocalCohomology.HasDimensionLE I d)
