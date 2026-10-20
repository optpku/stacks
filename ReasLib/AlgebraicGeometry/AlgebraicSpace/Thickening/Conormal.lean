/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Infinitesimal deformations of algebraic spaces

For a morphism of first-order thickenings of algebraic spaces whose map on the
closed subspaces is flat, flatness of the ambient map together with cartesianness
is equivalent to the canonical conormal comparison being an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

/-- For a morphism of first-order thickenings of algebraic spaces whose map on
closed subspaces is flat, the ambient map is flat and the square is cartesian if
and only if the canonical pullback comparison of conormal sheaves is an
isomorphism. -/
theorem flat_ambient_and_isPullback_iff_conormalMap_isIso
    {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S} {iX : X ⟶ X'} {iY : Y ⟶ Y'}
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY] {f : X ⟶ Y}
    {f' : X' ⟶ Y'} [Flat f] (sq : CommSq f iX iY f') :
    (Flat f' ∧ IsPullback f iX iY f') ↔ IsIso (Hom.Conormal.map sq) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
