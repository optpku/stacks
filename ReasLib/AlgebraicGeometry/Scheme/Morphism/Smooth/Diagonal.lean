/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.RingHom.Perfect.Basic

/-!
# Smooth morphisms and their diagonals

This file characterizes smooth morphisms of locally Noetherian schemes using properties of
their diagonals.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Smooth

/-- For a finite-type morphism of locally Noetherian schemes, smoothness is equivalent to
flatness together with the diagonal being a regular immersion, a local complete-intersection
morphism, or a perfect morphism. -/
theorem diagonal_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FiniteType f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] :
    List.TFAE [Smooth f,
      Flat f ∧ IsRegularImmersion (pullback.diagonal f),
      Flat f ∧ LocallyOfType RingHom.IsLocalCompleteIntersection (pullback.diagonal f),
      Flat f ∧ LocallyOfType RingHom.IsPerfectRingMap (pullback.diagonal f)] := sorry

end AlgebraicGeometry.Smooth
