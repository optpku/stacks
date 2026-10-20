/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Blowup.Triangle

open AlgebraicGeometry CategoryTheory
open RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.Cohomology
open AlgebraicGeometry.IsBlowup
open AlgebraicGeometry.IsBlowup.DeRham

/- Compatibility check for the canonical blowup comparison. -/
#check
  (@AlgebraicGeometry.IsBlowup.DeRham.toBlowup :
    ∀ {S X X' : Scheme} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
      [IsBlowup b I]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived
          (coefficientHom (relativeStructureSquare f I b)))
        (ModuleQis (RingedSpace.DeRham.coefficientSite (b ≫ f).toLRSHom.toShHom))],
      Scheme.DeRham.DerivedPushforward.derivedComplex f ⟶
        (modulePushforwardDerived
          (coefficientHom (relativeStructureSquare f I b))).obj
          (Scheme.DeRham.DerivedPushforward.derivedComplex (b ≫ f)))
