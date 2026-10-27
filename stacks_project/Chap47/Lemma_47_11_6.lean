/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Quotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/- Lemma 47.11.6 (1): for a finitely generated ideal `I`, the canonical comparison
identifies degree-zero ideal-power-torsion cohomology of `M` with degree-zero
cohomology supported on `V(I)`. -/
@[stacks 0AW0] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.h0IdealToClosedSupportIsIso :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ),
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
        ((idealToClosedSupport I hI RΓZ hRΓZ).app (ModuleCat.single0 M)).hom))

/- Lemma 47.11.6 (2): if `M' = M ⧸ I.primaryComponent M`, then
degree-zero ideal-power-torsion cohomology of `M'` vanishes. -/
@[stacks 0AW0] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.h0IdealQuotientPrimaryComponentIsZero :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A),
      letI : Fact I.FG := ⟨hI⟩
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
            CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).obj
          (ModuleCat.single0 (ModuleCat.of A (M ⧸ I.primaryComponent M)))).obj)))

section NoetherianIdealTorsion

variable [IsNoetherianRing A]

/- Lemma 47.11.6 (3): for `p > 0`, quotienting `M` by its common degree-zero
local-cohomology submodule `I.primaryComponent M` does not change degree-`p`
ideal-power-torsion cohomology over a Noetherian ring. -/
@[stacks 0AW0] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.idealCohomologyQuotientMapIsIsoOfPos :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A) (p : ℤ) (hp : 0 < p),
      letI : Fact I.FG := ⟨hI⟩
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) p).map
        (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
            CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).map
          (ModuleCat.single0Functor.map
            (ModuleCat.ofHom (Submodule.mkQ (I.primaryComponent M))))).hom)))

/- Lemma 47.11.6 (4): the positive-degree ideal-power-torsion cohomology of
the common degree-zero submodule `I.primaryComponent M` vanishes over a Noetherian ring. -/
@[stacks 0AW0] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.idealCohomologyPrimaryComponentIsZeroOfPos :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A) (p : ℤ) (hp : 0 < p),
      letI : Fact I.FG := ⟨hI⟩
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) p).obj
        (((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
            CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)).obj
          (ModuleCat.single0 (ModuleCat.of A (I.primaryComponent M)))).obj)))

end NoetherianIdealTorsion

/- Lemma 47.11.6 (5): if `M' = M ⧸ I.primaryComponent M`, then its
degree-zero cohomology supported on `V(I)` vanishes. -/
@[stacks 0AW0] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.h0ClosedSupportQuotientPrimaryComponentIsZero :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ),
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        ((RΓZ.obj
          (ModuleCat.single0 (ModuleCat.of A (M ⧸ I.primaryComponent M)))).obj)))

/- Lemma 47.11.6 (6): for `p > 0`, quotienting `M` by its common degree-zero
local-cohomology submodule `I.primaryComponent M` does not change degree-`p`
cohomology supported on `V(I)`. -/
@[stacks 0AW0] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.closedSupportCohomologyQuotientMapIsIsoOfPos :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) (p : ℤ) (hp : 0 < p),
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) p).map
        ((RΓZ.map (ModuleCat.single0Functor.map
          (ModuleCat.ofHom (Submodule.mkQ (I.primaryComponent M))))).hom)))

/- Lemma 47.11.6 (7): the positive-degree cohomology supported on `V(I)` of
the common degree-zero submodule `I.primaryComponent M` vanishes. -/
@[stacks 0AW0] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.closedSupportPrimaryComponentIsZeroOfPos :
    ∀ (I : Ideal A) (hI : I.FG) (M : ModuleCat.{u} A)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) (p : ℤ) (hp : 0 < p),
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) p).obj
        ((RΓZ.obj (ModuleCat.single0
          (ModuleCat.of A (I.primaryComponent M)))).obj)))

end CategoryTheory.DerivedCategory.LocalCohomology
