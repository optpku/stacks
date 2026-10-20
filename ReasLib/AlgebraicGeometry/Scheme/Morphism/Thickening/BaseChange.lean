/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace Thickening

/-- A pullback square of a thickening induces a morphism from the pullback thickening to
the original thickening. -/
noncomputable def pullbackHom {S S' X' : Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    [IsThickening i] :
    Thickening.of (pullback.snd i f') ⟶ Thickening.of i :=
  Thickening.homMk (pullback.fst i f') f' pullback.condition

end Thickening

namespace IsFirstOrderThickening

/-- The pullback of a first-order thickening is a first-order thickening. -/
instance pullbackSnd {S S' X' : Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    [IsFirstOrderThickening i] :
    IsFirstOrderThickening (pullback.snd i f') := sorry

end IsFirstOrderThickening

namespace IsFiniteOrderThickening

/-- The pullback of a finite-order thickening is a finite-order thickening. -/
instance pullbackSnd {S S' X' : Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    [IsFiniteOrderThickening i] :
    IsFiniteOrderThickening (pullback.snd i f') := sorry

end IsFiniteOrderThickening

end AlgebraicGeometry
