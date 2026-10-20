/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineExt
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.ULift

/-!
# Cohomology of affine derived internal Hom

The cohomology sheaf of an affine derived internal Hom is compared with the sheaf associated
to localized shifted Hom groups on principal opens.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- The universe-lifted underlying `n`th cohomology sheaf of an affine derived internal Hom. -/
noncomputable abbrev affineInternalHomCohomologySheaf
    {A : Type u} [CommRing A]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    TopCat.Sheaf AddCommGrpCat.{u + 1} (TopCat.of (PrimeSpectrum A)) :=
  (sheafCompose (Opens.grothendieckTopology (PrimeSpectrum A))
    AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      ((moduleUnderlyingSheaf (Spec (CommRingCat.of A)).toRingedSpace).obj
        (cohomologySheaf
          ((ihomOf H ((affineTildeDerived A).obj K)).obj
            ((affineTildeDerived A).obj L)) n))

/-- The principal open `D(f)` as an object of the standard basis of `Spec(A)`. -/
def affinePrincipalBasisOpen {A : Type u} [CommRing A] (f : A) :
    BasisOpen (Set.range fun g : PrincipalOpenIndex A ↦ (principalOpenFunctor A).obj g) :=
  ⟨PrimeSpectrum.basicOpen f, ⟨PrincipalOpenIndex.of f, rfl⟩⟩

/-- The restriction of affine internal-Hom cohomology to the standard principal-open basis. -/
noncomputable abbrev affineInternalHomCohomologyBasisSheaf
    {A : Type u} [CommRing A]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    BasisSiteSheaf AddCommGrpCat.{u + 1}
      (Set.range fun g : PrincipalOpenIndex A ↦ (principalOpenFunctor A).obj g) :=
  BasisSiteSheaf.restrict (principalOpenFunctor_isBasis A)
    (affineInternalHomCohomologySheaf H K L n)

/-- Evaluation of affine internal-Hom cohomology on `D(f)` is isomorphic to
`Ext^n_{A_f}(K ⊗ᴸ A_f, L ⊗ᴸ A_f)`. -/
theorem affineInternalHomCohomologyBasisSheaf_obj_isomorphic_affineExt
    {A : Type u} [CommRing A]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (f : A) :
    IsIsomorphic
      ((affineInternalHomCohomologyBasisSheaf H K L n).1.obj
        (op (affinePrincipalBasisOpen f) :
          (BasisOpen (Set.range fun g : PrincipalOpenIndex A ↦
            (principalOpenFunctor A).obj g))ᵒᵖ))
      (affineExtValue K L n f) := sorry

/-- The cohomology sheaf of an affine derived internal Hom is isomorphic to the sheafification
of its localized affine-Ext presheaf. -/
theorem affineInternalHomCohomologySheaf_isomorphic_affineExtSheaf
    {A : Type u} [CommRing A]
    [HasWeakSheafify (Opens.grothendieckTopology (PrimeSpectrum A))
      AddCommGrpCat.{u + 1}]
    [KFlat.HomotopyTensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.TensorDescends (Spec (CommRingCat.of A)).toRingedSpace]
    [KFlat.IsLocalization (Spec (CommRingCat.of A)).toRingedSpace]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (K L : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    IsIsomorphic (affineInternalHomCohomologySheaf H K L n)
      (affineExtSheaf K L n) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
