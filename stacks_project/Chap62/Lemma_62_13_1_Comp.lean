/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition

/-!
# Composition of families of cycles on fibres

The composition operation takes a family on fibres of `X / Y` and a family
on fibres of `Y / S` to a family on fibres of `X / S`.
-/

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp :
  ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℤ},
    Scheme.Hom.CyclesOnFibers f r → Scheme.Hom.CyclesOnFibers p e →
      Scheme.Hom.CyclesOnFibers (f ≫ p) (r + e))
