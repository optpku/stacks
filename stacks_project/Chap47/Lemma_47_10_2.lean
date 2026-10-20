/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CechComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 47.10.2 (1): if `f : Fin r → A` generates `I`, then the canonical map
from `RΓ_I(A)` to the extended alternating Cech complex of `f` with coefficients
in `A` is an isomorphism in `D(A)`. -/
@[stacks 0956] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.regularIdealToCechIsIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
      (hCech : IdealPowerTorsion.inclusion I ⊣
        CategoryTheory.DerivedCategory.LocalCohomology.cechFunctor I f hgen),
      IsIso (CategoryTheory.DerivedCategory.LocalCohomology.idealToCech
        I f hgen hCech DerivedCategory.CechCompletion.regular))

/- Lemma 47.10.2 (2): if `f : Fin r → A` generates `I` and `Z = V(I)`, then the
canonical map from the extended alternating Cech complex of `f` with coefficients
in `A` to `RΓ_Z(A)` is an isomorphism in `D(A)`. -/
@[stacks 0956] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.regularCechToClosedSupportIsIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
      (hCech : IdealPowerTorsion.inclusion I ⊣
        CategoryTheory.DerivedCategory.LocalCohomology.cechFunctor I f hgen)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ),
      IsIso (CategoryTheory.DerivedCategory.LocalCohomology.cechToClosedSupport
        I f hgen hCech RΓZ hRΓZ DerivedCategory.CechCompletion.regular))

/- Lemma 47.10.2 (3): if `f : Fin r → A` generates `I` and `M` is an
`A`-module, then the canonical map from `RΓ_I(M)` to the extended alternating
Cech complex of `f` with coefficients in `M` is an isomorphism in `D(A)`. -/
@[stacks 0956] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.moduleIdealToCechIsIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
      (hCech : IdealPowerTorsion.inclusion I ⊣
        CategoryTheory.DerivedCategory.LocalCohomology.cechFunctor I f hgen)
      (M : ModuleCat A),
      IsIso (CategoryTheory.DerivedCategory.LocalCohomology.idealToCech
        I f hgen hCech (ModuleCat.single0 M)))

/- Lemma 47.10.2 (4): if `f : Fin r → A` generates `I`, `Z = V(I)`, and `M`
is an `A`-module, then the canonical map from the extended alternating Cech
complex of `f` with coefficients in `M` to `RΓ_Z(M)` is an isomorphism in
`D(A)`. -/
@[stacks 0956] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.moduleCechToClosedSupportIsIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → A) (hgen : Ideal.span (Set.range f) = I)
      (hCech : IdealPowerTorsion.inclusion I ⊣
        CategoryTheory.DerivedCategory.LocalCohomology.cechFunctor I f hgen)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) (M : ModuleCat A),
      IsIso (CategoryTheory.DerivedCategory.LocalCohomology.cechToClosedSupport
        I f hgen hCech RΓZ hRΓZ (ModuleCat.single0 M)))

end CategoryTheory.DerivedCategory.LocalCohomology
