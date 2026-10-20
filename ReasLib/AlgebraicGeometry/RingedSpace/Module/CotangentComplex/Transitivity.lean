/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.InverseImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Transport
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Transitivity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain

/-!
# Transitivity for cotangent complexes of ringed spaces

The coefficient-tower triangle is transported to actual derived inverse image
using canonical comparisons of inverse-image presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape Opposite AlgebraicTopology TopologicalSpace
open CochainComplex HomotopyCategory SheafOfModules.RingedSite
open scoped Simplicial SheafOfModules.RingedSite.CotangentComplex AlgebraicGeometry

set_option backward.privateInPublic true

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X Y Z : RingedSpace.{u}}

/-- The cotangent complex of a morphism of ringed spaces, as an object of `D(O_X)`. -/
abbrev derived (f : X ⟶ Y) : DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (cotangentComplex f)

/-- Unfolding of `derived` as `DerivedCategory.Q` of `cotangentComplex`. -/
theorem derived_eq (f : X ⟶ Y) :
    derived f =
      (DerivedCategory.Q.obj (cotangentComplex f) : DerivedCategory X.Modules) :=
  rfl

/-- Cochain-level extension of scalars of `L(f⁻¹ g♯)` along `f♯`. -/
abbrev pullbackCochain (f : X ⟶ Y) (g : Y ⟶ Z) :
    CochainComplex X.Modules ℤ :=
  ((extendAlong (NaiveCotangent.Tower.second f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
    (CotangentComplex.obj _ (Under.mk (NaiveCotangent.Tower.first f g)))

/-- Unfolding of `pullbackCochain` as the sheaf-level tensor cochain of the coefficient tower. -/
theorem pullbackCochain_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCochain f g =
      CotangentComplex.tensorCochain (NaiveCotangent.Tower.first f g)
        (NaiveCotangent.Tower.second f) :=
  rfl

/-- The coefficient-tower tensor complex localized in the derived category. -/
abbrev pullbackCotangent (f : X ⟶ Y) (g : Y ⟶ Z) :
    DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (pullbackCochain f g)

/-- Unfolding of `pullbackCotangent` as `DerivedCategory.Q` of `pullbackCochain`. -/
theorem pullbackCotangent_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCotangent f g =
      (DerivedCategory.Q.obj (pullbackCochain f g) : DerivedCategory X.Modules) :=
  rfl

/-- Cotangent complexes of the iterated and composite coefficient maps agree
under the canonical isomorphism of inverse-image structure sheaves. -/
def compositionIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    CotangentComplex.obj _ (Under.mk (NaiveCotangent.Tower.composite f g)) ≅
      cotangentComplex (f ≫ g) :=
  (Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)).symm.app _ ≪≫
    (NatIso.mapHomologicalComplex (SheafOfModules.Restriction.idIso _) (up ℤ)).app _ ≪≫
    CotangentComplex.Transport.iso (NaiveCotangent.Tower.sourceIso f g)
      (Iso.refl X.sheaf) (NaiveCotangent.Tower.composite f g)
      (inverseImageStructureSheafHomComm (f ≫ g)) (by
        exact (RingedSpace.Hom.StructureSheaf.compositeMap_eq f g).symm.trans
          (Category.comp_id (NaiveCotangent.Tower.composite f g)).symm)

/-- The unextended first transitivity map `Lf^* L[g] ⟶ L[f ≫ g]`. -/
def transitivityMapCochain (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCochain f g ⟶ cotangentComplex (f ≫ g) :=
  CotangentComplex.tensorMapCochain (NaiveCotangent.Tower.first f g)
      (NaiveCotangent.Tower.second f) ≫
    (compositionIso f g).hom

/-- The localized first cotangent map of the coefficient tower. -/
def transitivityMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCotangent f g ⟶ derived (f ≫ g) :=
  DerivedCategory.Q.map (transitivityMapCochain f g)

/-- Unfolding of `transitivityMap` as `DerivedCategory.Q.map` of `transitivityMapCochain`. -/
theorem transitivityMap_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    transitivityMap f g = DerivedCategory.Q.map (transitivityMapCochain f g) :=
  rfl

/-- The unextended second transitivity map `L[f ≫ g] ⟶ L[f]`. -/
def toRelativeMapCochain (f : X ⟶ Y) (g : Y ⟶ Z) :
    cotangentComplex (f ≫ g) ⟶ cotangentComplex f :=
  (compositionIso f g).inv ≫
    CotangentComplex.toRelativeMapCochain (NaiveCotangent.Tower.first f g)
      (NaiveCotangent.Tower.second f)

/-- The second map `L[f ≫ g] ⟶ L[f]` of the transitivity triangle in `D(O_X)`. -/
def toRelativeMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    derived (f ≫ g) ⟶ derived f :=
  DerivedCategory.Q.map (toRelativeMapCochain f g)

/-- Unfolding of `toRelativeMap` as `DerivedCategory.Q.map` of `toRelativeMapCochain`. -/
theorem toRelativeMap_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    toRelativeMap f g = DerivedCategory.Q.map (toRelativeMapCochain f g) :=
  rfl

/-- The cotangent boundary into the positive-one shift of the coefficient-tower tensor. -/
def connectingMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    derived f ⟶ (pullbackCotangent f g)⟦(1 : ℤ)⟧ :=
  CotangentComplex.connectingMap (NaiveCotangent.Tower.first f g)
    (NaiveCotangent.Tower.second f)

/-- Unfolding of `connectingMap` as the sheaf-level connecting map of the coefficient tower. -/
theorem connectingMap_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    connectingMap f g =
      CotangentComplex.connectingMap (NaiveCotangent.Tower.first f g)
        (NaiveCotangent.Tower.second f) :=
  rfl

/-- Extending scalars along `f♯` identifies `f^* L[g]` with the tower tensor of
`f⁻¹ L[g]`. -/
def pullbackIso_inverseImage (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex g) ≅
      ((extendAlong (NaiveCotangent.Tower.second f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((SheafOfModules.RingedSite.InverseImage.modulePullback
              (Opens.map f.hom.base) Y.sheaf).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (cotangentComplex g)) :=
  SheafOfModules.RingedSite.InverseImage.Factorization.complexObjIso
    (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
    (Opens.map f.hom.base) (ComplexShape.up ℤ)
    (RingedSpace.Hom.commRingSheafPushforwardMap f) (cotangentComplex g)

/-- The forward map of `pullbackIso_inverseImage` is the module-pullback factorization. -/
theorem pullbackIso_inverseImage_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackIso_inverseImage f g).hom =
      (SheafOfModules.RingedSite.InverseImage.Factorization.complexObjIso
          (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X)
          (Opens.map f.hom.base) (ComplexShape.up ℤ)
          (RingedSpace.Hom.commRingSheafPushforwardMap f)
          (cotangentComplex g)).hom :=
  rfl

/-- The canonical comparison from derived inverse image to localized ordinary inverse
image on the standard cotangent representative. -/
def pullbackDerivedCounit (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePullbackDerived f).obj (derived g) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (cotangentComplex g)) :=
  (modulePullbackDerived f).map
      ((DerivedCategory.quotientCompQhIso Y.Modules).inv.app (cotangentComplex g)) ≫
    ((modulePullbackToDerived f).totalLeftDerivedCounit
        DerivedCategory.Qh (ModuleQis Y)).app
      ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj
        (cotangentComplex g)) ≫
    (Functor.Homotopy.cochainIso (RingedSpace.Hom.pullback f)).hom.app
      (cotangentComplex g)

/-- The derived counit on the bounded-above flat standard cotangent representative
is invertible. -/
instance pullbackDerivedCounit_isIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (pullbackDerivedCounit f g) :=
  sorry

/-- Localized ordinary pullback of the standard cotangent representative is canonically
isomorphic to its derived pullback. -/
def pullbackIso_derived (f : X ⟶ Y) (g : Y ⟶ Z) :
    DerivedCategory.Q.obj
        (((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (cotangentComplex g)) ≅
      (modulePullbackDerived f).obj (derived g) :=
  (asIso (pullbackDerivedCounit f g)).symm

/-- The inverse of `pullbackIso_derived` is `pullbackDerivedCounit`. -/
theorem pullbackIso_derived_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackIso_derived f g).inv = pullbackDerivedCounit f g :=
  rfl


namespace CotangentTransitivity

private def inverseImageSourceIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((InverseImage.modulePullback (J := Opens.grothendieckTopology Y)
      (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) Y.sheaf).mapHomologicalComplex
        (up ℤ)).obj (cotangentComplex g) ≅
    ((SheafOfModules.restrictScalars
      (ringSheafMap.{u, u, u} (J := Opens.grothendieckTopology X) ((OpensInverseImage.commRingInverseImageIso f).app Y.sheaf).inv)).mapHomologicalComplex
        (up ℤ)).obj
      (CotangentComplex.InverseImage.source (opensMorphismOfTopoi f)
        (inverseImageStructureSheafHomComm g)) :=
  (@NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
    (by infer_instance)
    (Functor.preservesZeroMorphisms_of_iso
      (OpensInverseImage.moduleInverseImageIso f Y.sheaf))
    (OpensInverseImage.moduleInverseImageIso f Y.sheaf) (up ℤ)).app (cotangentComplex g)

private def inverseImageTargetIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((SheafOfModules.restrictScalars
      (ringSheafMap.{u, u, u} (J := Opens.grothendieckTopology X) ((OpensInverseImage.commRingInverseImageIso f).app Y.sheaf).inv)).mapHomologicalComplex
        (up ℤ)).obj
      (CotangentComplex.InverseImage.target (opensMorphismOfTopoi f)
        (inverseImageStructureSheafHomComm g)) ≅
      CotangentComplex.obj _ (Under.mk (NaiveCotangent.Tower.first f g)) :=
  CotangentComplex.Transport.iso
    ((OpensInverseImage.commRingInverseImageIso f).app
      ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj Z.sheaf))
    ((OpensInverseImage.commRingInverseImageIso f).app Y.sheaf)
    ((opensMorphismOfTopoi f).commRingInverseImage.map
      (inverseImageStructureSheafHomComm g))
    (NaiveCotangent.Tower.first f g)
    ((OpensInverseImage.commRingInverseImageIso f).hom.naturality
      (inverseImageStructureSheafHomComm g)).symm

private def inverseImageModelIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((InverseImage.modulePullback (J := Opens.grothendieckTopology Y)
      (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) Y.sheaf).mapHomologicalComplex
        (up ℤ)).obj (cotangentComplex g) ≅
      CotangentComplex.obj _ (Under.mk (NaiveCotangent.Tower.first f g)) :=
  inverseImageSourceIso f g ≪≫
    ((SheafOfModules.restrictScalars
      (ringSheafMap.{u, u, u} (J := Opens.grothendieckTopology X) ((OpensInverseImage.commRingInverseImageIso f).app Y.sheaf).inv)).mapHomologicalComplex
        (up ℤ)).mapIso
      (CotangentComplex.InverseImage.iso (opensMorphismOfTopoi f)
        (inverseImageStructureSheafHomComm g)) ≪≫
    inverseImageTargetIso f g

end CotangentTransitivity

/-- Ordinary inverse image of the standard cotangent representative is canonically
isomorphic to the cotangent tensor complex of the coefficient tower. -/
def pullbackCochainIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((RingedSpace.Hom.pullback f).mapHomologicalComplex (up ℤ)).obj
      (cotangentComplex g) ≅ pullbackCochain f g :=
  pullbackIso_inverseImage f g ≪≫
    ((extendAlong (NaiveCotangent.Tower.second f)).mapHomologicalComplex (up ℤ)).mapIso
      (CotangentTransitivity.inverseImageModelIso f g)

/-- The localized coefficient-tower tensor is canonically isomorphic to actual
derived inverse image of the relative cotangent complex. -/
def pullbackCotangentIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCotangent f g ≅ (modulePullbackDerived f).obj (derived g) :=
  DerivedCategory.Q.mapIso (pullbackCochainIso f g).symm ≪≫ pullbackIso_derived f g

/-- The canonical cotangent triangle has derived inverse image as its first vertex. -/
def transitivityTriangle (f : X ⟶ Y) (g : Y ⟶ Z) :
    Triangle (DerivedCategory X.Modules) :=
  Triangle.mk ((pullbackCotangentIso f g).inv ≫ transitivityMap f g)
    (toRelativeMap f g)
    (connectingMap f g ≫
      (CategoryTheory.shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map (pullbackCotangentIso f g).hom)

/-- The first vertex is derived inverse image of the relative cotangent complex. -/
theorem transitivityTriangle_obj₁ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).obj₁ = (modulePullbackDerived f).obj (derived g) := rfl

/-- The second vertex is the cotangent complex of the composite morphism. -/
theorem transitivityTriangle_obj₂ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).obj₂ = derived (f ≫ g) := rfl

/-- The third vertex is the cotangent complex of the first morphism. -/
theorem transitivityTriangle_obj₃ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).obj₃ = derived f := rfl

/-- The first arrow is the coefficient-tower map transported from derived inverse image. -/
theorem transitivityTriangle_mor₁ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).mor₁ =
      (pullbackCotangentIso f g).inv ≫ transitivityMap f g := rfl

/-- The second arrow is the canonical relative cotangent map. -/
theorem transitivityTriangle_mor₂ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).mor₂ = toRelativeMap f g := rfl

/-- The boundary is transported to the positive-one shift of derived inverse image. -/
theorem transitivityTriangle_mor₃ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transitivityTriangle f g).mor₃ = connectingMap f g ≫
      (CategoryTheory.shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).map (pullbackCotangentIso f g).hom := rfl

/-- The canonical cotangent triangle of any composable pair of morphisms of ringed
spaces is distinguished in the derived category of modules on the source. -/
theorem transitivityTriangle_distinguished (f : X ⟶ Y) (g : Y ⟶ Z) :
    transitivityTriangle f g ∈ distTriang (DerivedCategory X.Modules) := by
  sorry

end AlgebraicGeometry.RingedSpace
