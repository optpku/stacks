/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PerfectAt
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.Perfect

/-!
# Perfect morphisms of algebraic spaces

The shared predicates and their scheme-level compatibility results are exposed
through their mathematical owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Perfectness of scheme morphisms is étale local on source-and-target. -/
#check (AlgebraicGeometry.LocallyOfType.isPerfectRingMap_isEtaleLocalAtSourceAndTarget :
  AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
    (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap))

namespace AlgebraicGeometry.AlgebraicSpace

/- On represented algebraic spaces, perfectness recovers perfectness of the
underlying scheme morphism. -/
#check (AlgebraicGeometry.AlgebraicSpace.perfect_ofOverMap_iff :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V),
    Perfect (ofOverMap h) ↔
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap h.left)

end AlgebraicGeometry.AlgebraicSpace
