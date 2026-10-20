module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 51.2.2 -/
@[stacks 0DWR] #check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.exists_tildeRestriction :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (F : (idealComplementOpens I).toScheme.Modules), ∀ [hF : F.IsQuasicoherent],
        ∃ M : ModuleCat A,
          IsIsomorphic ((AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι) F)

#check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.existsExactSequence :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (F : (idealComplementOpens I).toScheme.Modules), ∀ [hF : F.IsQuasicoherent],
        ∀ (M : ModuleCat A),
          ((AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F) →
            ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
              (IdealPowerTorsion.inclusion I ⊣ RΓ) →
                ∃ a : CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology I RΓ M 0 ⟶ M,
                  ∃ b : M ⟶ AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology I F 0,
                    ∃ c : AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology I F 0 ⟶
                      CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology I RΓ M 1,
                      Mono a ∧ (ComposableArrows.mk₃ a b c).Exact ∧ Epi c)

#check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.higherCohomology_isomorphic :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (F : (idealComplementOpens I).toScheme.Modules), ∀ [hF : F.IsQuasicoherent],
        ∀ (M : ModuleCat A),
          ((AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F) →
            ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
              (IdealPowerTorsion.inclusion I ⊣ RΓ) → ∀ (p : ℕ), 0 < p →
                IsIsomorphic
                  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology I F p)
                  (CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology I RΓ M
                    ((p + 1 : ℕ) : ℤ)))

#check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyZero_tildeRestriction_isomorphic :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (F : (idealComplementOpens I).toScheme.Modules), ∀ [hF : F.IsQuasicoherent],
        IsIsomorphic
          ((AlgebraicGeometry.tilde
              (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology I F 0 : ModuleCat A)).restrict
            (idealComplementOpens I).ι) F)

#check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyZero_supportedH0_isZero :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (F : (idealComplementOpens I).toScheme.Modules), ∀ [hF : F.IsQuasicoherent],
        ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
          (IdealPowerTorsion.inclusion I ⊣ RΓ) →
            IsZero (CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology I RΓ
              (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology I F 0) 0))

#check
  (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomologyZero_supportedH1_isZero :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (F : (idealComplementOpens I).toScheme.Modules), ∀ [hF : F.IsQuasicoherent],
        ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
          (IdealPowerTorsion.inclusion I ⊣ RΓ) →
            IsZero (CategoryTheory.DerivedCategory.LocalCohomology.supportedCohomology I RΓ
              (AlgebraicGeometry.Scheme.Modules.IdealComplement.cohomology I F 0) 1))
