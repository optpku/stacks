/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.StalkTorsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.10.4: The cohomology of a derived geometric stalk of a quasi-coherent
complex supported on a finitely presented closed subspace is power torsion for
the stalk of its defining ideal sheaf. -/
@[stacks 0AET] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.stalkDerived_cohomology_isIdealPowerTorsion :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
      [IsClosedImmersion i] [FinitePresentation i] (Q : DerivedQCoh X)
      (hQ : ModuleDerived.IsSupportedOn Q.obj (pointsImage i))
      (xbar : GeometricPoint X) (n : ℤ),
      Module.IsIdealPowerTorsion (Hom.idealSheafStalkIdeal i xbar)
        ((DerivedCategory.homologyFunctor (ModuleCat (etaleLocalRing X xbar)) n).obj
          (ModuleDerived.stalkDerived xbar Q.obj)))
