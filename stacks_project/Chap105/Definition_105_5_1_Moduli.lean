/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.Moduli

/-! The concrete moduli category of elliptic curves and its classifying morphisms. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.EllipticCurve.moduli :
  GroupoidsOver AlgebraicGeometry.EllipticCurve.Moduli.specInt.{u})

#check (AlgebraicGeometry.EllipticCurve.Moduli.classifying :
  ∀ (U : Over AlgebraicGeometry.EllipticCurve.Moduli.specInt.{u})
    (E : Over U.left) (zero : U.left ⟶ E.left)
    [AlgebraicGeometry.EllipticCurve.IsEllipticCurve E zero],
    GroupoidsOver.slice U ⟶ AlgebraicGeometry.EllipticCurve.moduli.{u})
