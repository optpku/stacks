module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Vanishing
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 47.9.4: if `I` is finitely generated and some `f ∈ I` acts invertibly on a
derived `A`-module `K`, then any right adjoint to the inclusion of derived modules with
`I`-power-torsion cohomology sends `K` to zero. -/
@[stacks 0A6S]
#check (CategoryTheory.DerivedCategory.LocalCohomology.isZero_of_isIso_smul :
  ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
    ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
      (IdealPowerTorsion.inclusion I ⊣ RΓ) →
        ∀ {f : A}, f ∈ I → ∀ (K : DerivedCategory (ModuleCat A))
          [IsIso (f • 𝟙 K)], IsZero (RΓ.obj K))

/- The localization-away specialization has the complete expected type. -/
#check
  (CategoryTheory.DerivedCategory.LocalCohomology.isZero_of_mem_localizationAway_essImage :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
        (IdealPowerTorsion.inclusion I ⊣ RΓ) →
          ∀ {f : A}, f ∈ I → ∀ {K : DerivedCategory (ModuleCat A)},
            (ModuleCat.derivedRestrictionOfScalars
              (algebraMap A (Localization.Away f))).essImage K →
              IsZero (RΓ.obj K))

end CategoryTheory.DerivedCategory.LocalCohomology
