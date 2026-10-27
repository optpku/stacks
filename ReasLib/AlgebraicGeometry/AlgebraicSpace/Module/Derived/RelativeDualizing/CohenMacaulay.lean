/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Family
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.StalkFlatness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.LeftDerived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction

/-! # Relative dualizing complexes of Cohen–Macaulay families of curves -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

variable {S : Scheme.{u}}

/-- The relative dualizing complex of a Cohen–Macaulay family of curves of
relative dimension 1 is bounded above by degree `-1`. -/
theorem isLE_negOne {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    C.complex.IsLE (-1) :=
  sorry

/-- The relative dualizing complex of a Cohen–Macaulay family of curves of
relative dimension 1 is bounded below by degree `-1`. -/
theorem isGE_negOne {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    C.complex.IsGE (-1) :=
  sorry

/-- The relative dualizing complex of a Cohen–Macaulay family of curves of
relative dimension 1 is the shift by `1` of its degree `-1` cohomology sheaf. -/
theorem isIsomorphic_cohomologySheaf_shift {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    IsIsomorphic C.complex
      (((DerivedCategory.singleFunctor (Modules X) 0).obj
          (cohomologySheaf C.complex (-1)))⟦(1 : ℤ)⟧) :=
  sorry

/-- The degree `-1` cohomology sheaf of the relative dualizing complex of a
Cohen–Macaulay family of curves of relative dimension 1, viewed in degree `0`,
is a pseudo-coherent derived `𝒪_X`-module. -/
theorem cohomologySheaf_isPseudoCoherent {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    IsPseudoCoherent X
      ((DerivedCategory.singleFunctor (Modules X) 0).obj
        (cohomologySheaf C.complex (-1))) :=
  sorry

/-- The degree `-1` cohomology sheaf of the relative dualizing complex of a
Cohen–Macaulay family of curves of relative dimension 1 is flat over the base. -/
theorem cohomologySheaf_flatOver {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    ∀ sq : EtaleSquare f,
      Scheme.Modules.IsStalkFlatOver
        ((Modules.restrictToScheme sq.left.left).obj
          ((Modules.pullback sq.left.hom).obj (cohomologySheaf C.complex (-1))))
        sq.map.left :=
  sorry

/-- Formation of the degree `-1` cohomology sheaf of the relative dualizing
complex of a Cohen–Macaulay family of curves of relative dimension 1 commutes
with arbitrary base change. -/
theorem cohomologySheaf_baseChange {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) {X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [∀ sq : EtaleSquare f',
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f',
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] (g : Y' ⟶ Y)
    [IsFamily f'] [CohenMacaulay f'] [RelativeDimension f' 1]
    (sq : IsPullback g' f' f g) (C' : RelativeDualizingComplex f') :
    IsIsomorphic
      ((Modules.pullback g').obj (cohomologySheaf C.complex (-1)))
      (cohomologySheaf C'.complex (-1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
