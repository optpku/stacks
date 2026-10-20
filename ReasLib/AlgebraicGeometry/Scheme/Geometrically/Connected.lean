/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometrically connected scheme morphisms

This module characterizes geometric connectedness over a field in terms of
connectedness after every field extension.
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

namespace GeometricallyConnected

/-- A morphism from a scheme to the spectrum of a field is geometrically connected if and only if
its pullback along every field extension has connected underlying space. -/
theorem iff_connectedSpace_baseChange :
    GeometricallyConnected f ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace ((pullback f (Spec.map <| ofHom <| algebraMap k K)) : Scheme) := sorry

end GeometricallyConnected

end AlgebraicGeometry
