module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion
import StacksCheckRecall

open CategoryTheory

noncomputable section

universe u

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)

/- Lemma 47.8.1: for a finitely generated ideal `I` of a commutative ring `A`, the
total right-derived ideal-power-torsion functor `RΓ_I` is right adjoint to the derived
inclusion `D(I^∞-torsion) ⥤ D(A)`. -/
@[stacks 0A6L] #check
  (CategoryTheory.ModuleCat.IdealPowerTorsion.derivedAdjunctionOfFG I hI :
    CategoryTheory.ModuleCat.IdealPowerTorsion.derivedInclusion I ⊣
      CategoryTheory.ModuleCat.IdealPowerTorsion.derivedTorsion I)
