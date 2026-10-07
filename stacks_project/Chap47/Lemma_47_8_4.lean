module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.8.4 -/
@[stacks 0A6P]
#check (CategoryTheory.ModuleCat.IdealPowerTorsion.derivedInclusion_hom_bijective :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : ModuleCat.IdealPowerTorsion.category I),
    Function.Bijective (fun f :
      (DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj M ⟶
        (DerivedCategory.singleFunctor (ModuleCat.IdealPowerTorsion.category I) 0).obj N ↦
      (ModuleCat.IdealPowerTorsion.derivedInclusion I).map f))

#check CategoryTheory.ModuleCat.IdealPowerTorsion.derivedInclusion_extOne_bijective
#check CategoryTheory.ModuleCat.IdealPowerTorsion.exists_derivedInclusion_extTwo_not_surjective
#check CategoryTheory.ModuleCat.IdealPowerTorsion.exists_comparison_not_equivalence
