/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion.Comparison

@[expose] public section

open CategoryTheory
open DerivedCategory.CechCompletion

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The comparison from derived ideal-power torsion to the extended alternating Cech complex
associated to a finite generating family. -/
noncomputable def idealToCech {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I)
    (hCech : IdealPowerTorsion.inclusion I ⊣ cechFunctor I f hgen)
    (K : DerivedCategory (ModuleCat A)) :=
  (IdealPowerTorsion.inclusion I).map
      ((idealToClosedSupport I (Ideal.fg_of_isNoetherianRing I)
        (cechFunctor I f hgen) hCech).app K) ≫
    eqToHom (cechFunctor_obj I f hgen K)

/-- The comparison from the extended alternating Cech complex associated to a finite generating
family to a chosen closed-support right adjoint. -/
noncomputable def cechToClosedSupport {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I)
    (hCech : IdealPowerTorsion.inclusion I ⊣ cechFunctor I f hgen)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :=
  eqToHom (cechFunctor_obj I f hgen K).symm ≫
    (IdealPowerTorsion.inclusion I).map
      ((Adjunction.rightAdjointUniq hCech hRΓZ).hom.app K)

/-- For the regular module, the comparison from derived ideal-power torsion to the extended
alternating Cech complex of a finite generating family is an isomorphism. -/
noncomputable instance regularIdealToCechIsIso {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I)
    (hCech : IdealPowerTorsion.inclusion I ⊣ cechFunctor I f hgen) :
    IsIso (idealToCech I f hgen hCech regular) := sorry

/-- For the regular module, the comparison from the extended alternating Cech complex of a finite
generating family to a chosen closed-support right adjoint is an isomorphism. -/
noncomputable instance regularCechToClosedSupportIsIso {r : ℕ} (I : Ideal A)
    (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
    (hCech : IdealPowerTorsion.inclusion I ⊣ cechFunctor I f hgen)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    IsIso (cechToClosedSupport I f hgen hCech RΓZ hRΓZ regular) := sorry

/-- For an arbitrary module, the comparison from derived ideal-power torsion to the extended
alternating Cech complex of a finite generating family is an isomorphism. -/
noncomputable instance moduleIdealToCechIsIso {r : ℕ} (I : Ideal A) (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = I)
    (hCech : IdealPowerTorsion.inclusion I ⊣ cechFunctor I f hgen)
    (M : ModuleCat A) :
    IsIso (idealToCech I f hgen hCech (ModuleCat.single0 M)) := sorry

/-- For an arbitrary module, the comparison from the extended alternating Cech complex of a finite
generating family to a chosen closed-support right adjoint is an isomorphism. -/
noncomputable instance moduleCechToClosedSupportIsIso {r : ℕ} (I : Ideal A)
    (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
    (hCech : IdealPowerTorsion.inclusion I ⊣ cechFunctor I f hgen)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) (M : ModuleCat A) :
    IsIso (cechToClosedSupport I f hgen hCech RΓZ hRΓZ (ModuleCat.single0 M)) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
