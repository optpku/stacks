/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.Classes
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Perfect

/-!
# Perfectness on represented algebraic spaces

Perfectness of a morphism between represented algebraic spaces agrees with
perfectness of the underlying scheme morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism between represented algebraic spaces is perfect exactly when
the underlying scheme morphism is perfect. -/
theorem perfect_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Perfect (ofOverMap h) ↔
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap h.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
