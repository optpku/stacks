/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-! # Relative dualizing sheaves of Cohen–Macaulay and Gorenstein families of curves -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- The relative dualizing sheaf of a Cohen–Macaulay family of curves of
relative dimension 1 is the degree `-1` cohomology sheaf of the chosen
relative dualizing complex. -/
noncomputable def sheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) : X.Modules :=
  cohomologySheaf C.complex (-1)

/-- The relative dualizing sheaf is the degree `-1` cohomology sheaf of the
chosen relative dualizing complex. -/
theorem sheaf_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    sheaf C = cohomologySheaf C.complex (-1) :=
  rfl

/-- The degree `-1` cohomology sheaf of a relative dualizing complex of a
Gorenstein family of curves of relative dimension 1 is tensor-invertible. -/
theorem cohomologySheaf_isInvertible {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [Gorenstein f]
    [RelativeDimension f 1] (C : RelativeDualizingComplex f) :
    isInvertibleObject (cohomologySheaf C.complex (-1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
