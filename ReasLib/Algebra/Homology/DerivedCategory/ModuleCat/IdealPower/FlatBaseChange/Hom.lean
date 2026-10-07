module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.FlatBaseChange
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Flat base change inducing an isomorphism modulo a finitely generated ideal
gives bijections on all shifted Hom sets out of complexes with ideal-power-torsion
cohomology. -/
theorem shiftedHomMap_bijective
    (f : A →+* B) (I : Ideal A) (hI : I.FG) (hf : f.Flat)
    (hquot : Function.Bijective (f.quotientByIdeal I))
    (K : DerivedCategory.CohomologyIn
      (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M))
    (L : DerivedCategory (ModuleCat A)) (i : ℤ) :
    Function.Bijective (fun e : ShiftedHom K.obj L i ↦
      e.map (ModuleCat.derivedExtensionOfScalars f)) := sorry

end CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange
