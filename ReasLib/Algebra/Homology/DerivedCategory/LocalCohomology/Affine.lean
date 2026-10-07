module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Support

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

open AlgebraicGeometry

/-- For a finitely generated ideal, local cohomology is isomorphic to derived global sections
on the affine scheme supported on the corresponding zero locus. -/
theorem affineComparison_isomorphic {A : CommRingCat.{u}}
    (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) :
    IsIsomorphic (RΓ ⋙ IdealPowerTorsion.inclusion I)
      (Scheme.DerivedQCoh.affineGlobalSectionsWithSupport I) := sorry

/-- Objectwise, local cohomology is isomorphic to derived global sections supported on the
zero locus of a finitely generated ideal. -/
theorem affineComparison_obj_isomorphic {A : CommRingCat.{u}}
    (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K : DerivedCategory (ModuleCat A)) :
    IsIsomorphic ((IdealPowerTorsion.inclusion I).obj (RΓ.obj K))
      ((Scheme.DerivedQCoh.affineGlobalSectionsWithSupport I).obj K) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
