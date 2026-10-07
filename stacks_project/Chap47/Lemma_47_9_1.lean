module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.9.1: For a finitely generated ideal, the inclusion of derived modules with
ideal-power-torsion cohomology admits a right adjoint. -/
@[stacks 0A6R] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.existsRightAdjoint :
    ∀ {A : Type u} [CommRing A] (I : Ideal A), I.FG →
      ∃ RΓ : (DerivedCategory (ModuleCat A) ⥤
          CategoryTheory.DerivedCategory.IdealPowerTorsion I),
        Nonempty
          (CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ))

#check
  (CategoryTheory.DerivedCategory.LocalCohomology.cechAdjunction :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A) (f : Fin r → A)
      (hgen : Ideal.span (Set.range f) = I),
      Nonempty
        (CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣
          CategoryTheory.DerivedCategory.LocalCohomology.cechFunctor I f hgen))

#check
  (CategoryTheory.DerivedCategory.LocalCohomology.cechFunctorCompιIso :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (I : Ideal A) (f : Fin r → A)
      (hgen : Ideal.span (Set.range f) = I),
      (CategoryTheory.DerivedCategory.LocalCohomology.cechFunctor I f hgen ⋙
          CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I) ≅
        CategoryTheory.DerivedCategory.DerivedTensor.Left.functor
          (DerivedCategory.CechCompletion.source f))
