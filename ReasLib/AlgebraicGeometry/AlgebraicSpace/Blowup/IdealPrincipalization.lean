/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RegularAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.FinitePointSequence
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-!
# Principalization of finitely supported ideals on algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-coherent ideal on a Noetherian algebraic space whose quotient is supported on
finitely many closed regular points with two-dimensional local rings becomes invertible
after finitely many blowups at closed points lying over that support. -/
theorem existsInvertibleIdealAfterPointBlowups {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsNoetherian X] (T : Set (Points X))
    (hT_finite : T.Finite) (hT_closed : T ⊆ closedPoints (Points X))
    (hT_regular : ∀ x, x ∈ T → RegularAt X x)
    (hT_dimension : ∀ x, x ∈ T → localRingDimAt x = 2)
    (I : IdealSubobject X) [IsQuasiCoherent I]
    (hI_support : (ClosedSubspace.ofQuasiCoherentIdeal I).pointsSet ⊆ T) :
    ∃ (Xn : AlgebraicSpace S) (s : PointBlowupSequence X Xn),
      s.EveryCenterOver T ∧ isInvertibleObject (I.pullback s.toSource).toModule :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
