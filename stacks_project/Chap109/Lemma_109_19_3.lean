/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.RelativeDualizingSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.CohenMacaulay
import StacksCheckRecall

/-!
# Relative dualizing sheaf of a Gorenstein family of curves

For a family of curves with Gorenstein fibres equidimensional of dimension 1,
the degree `-1` cohomology sheaf of a relative dualizing complex is an
invertible `𝒪_X`-module, and its formation commutes with arbitrary base change.
The canonical instance from Gorenstein to Cohen–Macaulay morphisms makes the
Cohen–Macaulay base-change theorem applicable to these families.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.19.3: the relative dualizing sheaf of a Gorenstein family of
curves equidimensional of dimension 1 is invertible, and its formation
commutes with arbitrary base change. -/
@[stacks 0E6R]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.cohomologySheaf_isInvertible :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [Gorenstein f]
    [RelativeDimension f 1] (C : RelativeDualizingComplex f),
    isInvertibleObject (cohomologySheaf C.complex (-1)))

/- Formation of the relative dualizing sheaf commutes with arbitrary base
change for Cohen–Macaulay families, hence for Gorenstein families. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.cohomologySheaf_baseChange :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
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
    (sq : IsPullback g' f' f g) (C' : RelativeDualizingComplex f'),
    IsIsomorphic
      ((Modules.pullback g').obj (cohomologySheaf C.complex (-1)))
      (cohomologySheaf C'.complex (-1)))
