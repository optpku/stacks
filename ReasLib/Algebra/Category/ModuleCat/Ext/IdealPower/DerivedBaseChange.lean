module

public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.FlatBaseChange.Hom

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.Ext.IdealPower.DerivedBaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Flat base change inducing an isomorphism modulo a finitely generated ideal
gives bijections on Ext in every degree out of ideal-power-torsion modules. -/
theorem map_bijective
    (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (M N : ModuleCat.{u} A) (hf : f.Flat)
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : Function.Bijective (f.quotientByIdeal I)) (i : ℕ) :
    Function.Bijective
      (CategoryTheory.ModuleCat.Ext.FlatBaseChange.map f M N hf i) := sorry

end CategoryTheory.ModuleCat.Ext.IdealPower.DerivedBaseChange
