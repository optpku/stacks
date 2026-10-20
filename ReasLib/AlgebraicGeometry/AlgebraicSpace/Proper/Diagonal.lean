/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.Data.List.TFAE

/-!
# Separatedness via the relative diagonal

A morphism of algebraic spaces is separated iff its relative diagonal is
universally closed, iff that same diagonal is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Separated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A morphism of algebraic spaces is separated if and only if its relative
diagonal is universally closed, if and only if that diagonal is proper. -/
theorem tfae_diagonal (f : X ⟶ Y) :
    List.TFAE [Separated f, UniversallyClosed (pullback.diagonal f),
      Proper (pullback.diagonal f)] :=
  sorry

/-- A morphism of algebraic spaces is separated if and only if its relative
diagonal is universally closed. -/
theorem iff_universallyClosed_diagonal (f : X ⟶ Y) :
    Separated f ↔ UniversallyClosed (pullback.diagonal f) :=
  (tfae_diagonal f).out 0 1

/-- A morphism of algebraic spaces is separated if and only if its relative
diagonal is proper. -/
theorem iff_proper_diagonal (f : X ⟶ Y) :
    Separated f ↔ Proper (pullback.diagonal f) :=
  (tfae_diagonal f).out 0 2

/-- The relative diagonal of a separated morphism of algebraic spaces is
universally closed. -/
instance universallyClosed_diagonal {f : X ⟶ Y} [Separated f] :
    UniversallyClosed (pullback.diagonal f) :=
  (iff_universallyClosed_diagonal f).mp inferInstance

/-- The relative diagonal of a separated morphism of algebraic spaces is
proper. -/
instance proper_diagonal {f : X ⟶ Y} [Separated f] :
    Proper (pullback.diagonal f) :=
  (iff_proper_diagonal f).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace.Separated
