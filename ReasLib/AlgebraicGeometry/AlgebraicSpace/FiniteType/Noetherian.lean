/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite-type separated algebraic space over a Noetherian affine base is Noetherian. -/
instance instIsNoetherian_of_finiteType_toBase
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)] :
    IsNoetherian X := sorry

end AlgebraicGeometry.AlgebraicSpace
