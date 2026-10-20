/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Conormal
import StacksCheckRecall

/-!
# Infinitesimal deformations of algebraic spaces

The conormal flatness criterion for morphisms of first-order thickenings.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme AlgebraicSpace)
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.18.1: For a morphism of first-order thickenings with flat map on
closed subspaces, the ambient map is flat and the square is cartesian if and
only if the canonical conormal comparison is an isomorphism. -/
@[stacks 06BH] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.flat_ambient_and_isPullback_iff_conormalMap_isIso :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S} {iX : X ⟶ X'} {iY : Y ⟶ Y'}
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY] {f : X ⟶ Y}
    {f' : X' ⟶ Y'} [Flat f] (sq : CommSq f iX iY f'),
    (Flat f' ∧ IsPullback f iX iY f') ↔ IsIso (Hom.Conormal.map sq))
