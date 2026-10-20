/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open AlgebraicGeometry
open LocalCohomology
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace IdealComplement

/- Lemma 51.8.2 (1): a coherent module on `Spec A ∖ V(I)` is the restriction of
the tilde module of some finite `A`-module. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.existsFiniteExtension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent],
      ∃ M : ModuleCat A, Module.Finite A M ∧
        IsIsomorphic ((AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι) F)

/- Lemma 51.8.2 (2): a finite extension of `F` yields the five-term exact sequence
from supported cohomology to cohomology on `Spec A ∖ V(I)`. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.existsExactSequence_of_finiteExtension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
      (M : ModuleCat A) [Module.Finite A M]
      (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
      (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ),
      ∃ a : supportedCohomology I RΓ M 0 ⟶ M,
        ∃ b : M ⟶ cohomology I F 0,
          ∃ c : cohomology I F 0 ⟶ supportedCohomology I RΓ M 1,
            Mono a ∧ (ComposableArrows.mk₃ a b c).Exact ∧ Epi c)

/- Lemma 51.8.2 (3): positive-degree cohomology on `Spec A ∖ V(I)` is the
next supported-cohomology module of a finite extension. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.higherCohomology_isomorphic_of_finiteExtension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
      (M : ModuleCat A) [Module.Finite A M]
      (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
      (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) (p : ℕ) (hp : 0 < p),
      IsIsomorphic (cohomology I F p)
        (supportedCohomology I RΓ M ((p + 1 : ℕ) : ℤ)))

/- Lemma 51.8.2 (4): the `p`-th higher direct image of `F` is coherent exactly
when the corresponding cohomology module on `Spec A ∖ V(I)` is finite. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.higherDirectImage_isCoherent_iff_cohomology_finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent] (p : ℕ),
      (RingedSpace.Hom.higherDirectImageModule
        (idealComplementOpens I).ι.toShHom F p).IsCoherent ↔
        Module.Finite A (cohomology I F p))

/- Lemma 51.8.2 (5): for a finite extension and every `p`, including `p = 0`,
finiteness of cohomology on `Spec A ∖ V(I)` is equivalent to finiteness of the
next supported cohomology. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology_finite_iff_supportedCohomology_finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
      (M : ModuleCat A) [Module.Finite A M]
      (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
      (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) (p : ℕ),
      Module.Finite A (cohomology I F p) ↔
        Module.Finite A (supportedCohomology I RΓ M ((p + 1 : ℕ) : ℤ)))

/- Lemma 51.8.2 (6): when degree-zero cohomology is finite, it gives the
canonical finite extension whose tilde module restricts to `F`. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyZero_tildeRestriction_isomorphic_of_finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
      [Module.Finite A (cohomology I F 0)],
      IsIsomorphic
        ((AlgebraicGeometry.tilde (cohomology I F 0 : ModuleCat A)).restrict
          (idealComplementOpens I).ι) F)

/- Lemma 51.8.2 (7): the canonical finite degree-zero extension has vanishing
degree-zero supported cohomology. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyZero_supportedH0_isZero_of_finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
      [Module.Finite A (cohomology I F 0)]
      (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ),
      IsZero (supportedCohomology I RΓ (cohomology I F 0) 0))

/- Lemma 51.8.2 (8): the canonical finite degree-zero extension has vanishing
degree-one supported cohomology. -/
@[stacks 0BK0] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyZero_supportedH1_isZero_of_finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
      [Module.Finite A (cohomology I F 0)]
      (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ),
      IsZero (supportedCohomology I RΓ (cohomology I F 0) 1))

end IdealComplement
end AlgebraicGeometry.Scheme.Modules
