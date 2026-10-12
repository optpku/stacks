/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Quotient
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.CategoryTheory.DerivedCategory.Colimit.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological.IsOf

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTorsion

open DerivedCategory DerivedCategory.InternalHom.RHom

/-- The derived ideal-power torsion of a complex is the homotopy colimit of the
canonical derived Hom tower from the positive ideal-power quotients. -/
theorem derivedTorsionIsHomotopyColimit
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{u} A)) :
      HomotopyColimit.IsOf
      ((DerivedCategory.IdealPower.system I).rightOp ⋙
        DerivedCategory.InternalHom.RHom.sourceFunctor K)
      ((derivedInclusion I).obj ((derivedTorsion I).obj K)) := sorry

/-- In every integer degree, the homology of derived ideal-power torsion is the
categorical colimit of the homologies of its positive quotient derived Hom tower. -/
theorem derivedTorsionHomologyIsColimit
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{u} A)) (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
        ((derivedInclusion I).obj ((derivedTorsion I).obj K)))
      (colimit
        (((DerivedCategory.IdealPower.system I).rightOp ⋙
            DerivedCategory.InternalHom.RHom.sourceFunctor K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) q)) := sorry

end CategoryTheory.ModuleCat.IdealPowerTorsion

end
