/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Derived
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Affine
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Derived eta for ideal sheaves on schemes

The derived eta functor of an effective Cartier ideal sheaf preserves complexes with
quasicoherent cohomology. On a principal affine scheme, the restricted functor corresponds to
the ring-level derived eta functor under affine derived global sections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.Eta.Derived

variable {X : Scheme.{u}}

/-- Derived ideal-sheaf eta preserves complexes with quasicoherent cohomology. -/
theorem mapsTo (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).inverseImage
          (RingedSpace.IdealSheaf.Eta.Derived.functor D.toSubobject) := sorry

/-- Derived ideal-sheaf eta restricted to complexes with quasicoherent cohomology. -/
noncomputable def functor (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  ObjectProperty.FullSubcategory.restrict
    (RingedSpace.IdealSheaf.Eta.Derived.functor D.toSubobject) (mapsTo D)

/-- Forgetting the restricted derived eta functor recovers the ambient derived eta functor. -/
noncomputable def inclusionIso (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    functor D ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ≅
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          RingedSpace.IdealSheaf.Eta.Derived.functor D.toSubobject :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (RingedSpace.IdealSheaf.Eta.Derived.functor D.toSubobject) (mapsTo D)

/-- The forward inclusion comparison for restricted derived eta is componentwise the identity. -/
theorem inclusionIso_hom_app (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) :
    (inclusionIso D).hom.app E =
      𝟙 ((RingedSpace.IdealSheaf.Eta.Derived.functor D.toSubobject).obj E.obj) := sorry

/-- On a principal affine scheme, restricted ideal-sheaf derived eta corresponds to the
ring-level derived eta functor under affine derived global sections. -/
theorem affineComparison_isomorphic (A : CommRingCat.{u})
    (D : (Spec A).IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (f : nonZeroDivisors A)
    (hD : D = Scheme.idealSheafDataOfIdealOnSpec (Ideal.span {(f : A)})) :
    IsIsomorphic
      (functor D ⋙ Scheme.DerivedQCoh.affineGlobalSections A)
      (Scheme.DerivedQCoh.affineGlobalSections A ⋙
        CochainComplex.BerthelotOgus.Int.Derived.functor f) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData.Eta.Derived
