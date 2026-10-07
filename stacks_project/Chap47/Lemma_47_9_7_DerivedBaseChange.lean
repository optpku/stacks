module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.FlatBaseChange

open CategoryTheory

universe u

#check
  (CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange.unitCounit_isIso :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
        (f : A →+* B) (I : Ideal A) (hI : I.FG) (hf : f.Flat)
        (hquot : Function.Bijective (f.quotientByIdeal I)),
      (∀ K : DerivedCategory.CohomologyIn
          (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M),
        IsIso
          ((CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange.adjunction
            f I hf).unit.app K)) ∧
      (∀ L : DerivedCategory.CohomologyIn
          (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M),
        IsIso
          ((CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange.adjunction
            f I hf).counit.app L)))
