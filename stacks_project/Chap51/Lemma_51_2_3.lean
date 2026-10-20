module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.SupportRestriction
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 51.2.3 -/
@[stacks 0DWS] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.supportRestrictionMapIsIso :
    {A : Type u} → [CommRing A] →
      (I J : Ideal A) → (hI : I.FG) → (hJ : J.FG) →
      (M : ModuleCat A) → (hM : Module.IsIdealPowerTorsion I M) →
      (RΓJ : DerivedCategory (ModuleCat A) ⥤ DerivedCategory.IdealPowerTorsion J) →
      (RΓIJ : DerivedCategory (ModuleCat A) ⥤
        DerivedCategory.IdealPowerTorsion (I ⊔ J)) →
      (hRΓJ : DerivedCategory.IdealPowerTorsion.inclusion J ⊣ RΓJ) →
      (hRΓIJ : DerivedCategory.IdealPowerTorsion.inclusion (I ⊔ J) ⊣ RΓIJ) →
      (i : ℤ) →
      IsIso (CategoryTheory.DerivedCategory.LocalCohomology.supportRestrictionMap
        I J hI hJ M hM RΓJ RΓIJ hRΓJ hRΓIJ i))
