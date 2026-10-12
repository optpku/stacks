/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Duality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedExt

universe u

/- Compatibility: derived global cohomology over the ground field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (K : AlgebraicGeometry.Scheme.DerivedQCoh X) (i : ℤ), ModuleCat.{u} k)

/- Compatibility: unfolding of cohomology over the field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField_def :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (K : AlgebraicGeometry.Scheme.DerivedQCoh X) (i : ℤ),
      AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField f K i =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections (CommRingCat.of k)).obj
            ((AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj (K⟦i⟧))))

/- Compatibility: functoriality of proper cohomology over the field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverFieldMap :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      {K L : AlgebraicGeometry.Scheme.DerivedQCoh X} (a : K ⟶ L) (i : ℤ),
      AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField f K i ⟶
        AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField f L i)

/- Compatibility: affine-derived model of the ground field. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject :
    ∀ (k : Type u) [Field k], ModuleCat.{u} k)

/- Compatibility: unfolding of the affine-derived field object. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject_def :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject k =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSections (CommRingCat.of k)).obj
            (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k)))))

/- Compatibility: identification of the affine-derived field object with `ModuleCat.of k k`. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject_isomorphic_field :
    ∀ (k : Type u) [Field k],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject k)
        (ModuleCat.of k k))

/- Compatibility: Ext-to-Hom comparison for the proper dualizing complex. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.extComparison :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (i : ℤ) (K : AlgebraicGeometry.Scheme.DerivedQCoh X),
      Ext⁽i⁾(K, AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f) →
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField f K (-i) ⟶
          AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject k))

/- Compatibility: degree-zero derived object of a quasicoherent module. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleObject :
    ∀ {X : Scheme.{u}} (F : AlgebraicGeometry.Scheme.QCoh X),
      AlgebraicGeometry.Scheme.DerivedQCoh X)

/- Compatibility: module duality comparison for quasicoherent sheaves. -/
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleDualityComparison :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (F : AlgebraicGeometry.Scheme.QCoh X),
      (((AlgebraicGeometry.Scheme.QCoh.toRingedSpace X).obj F).obj ⟶
          AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule f) →
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField f
            (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleObject F)
            (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dimensionIndex f) ⟶
          AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject k))
