/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTransport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-! # Representability and ampleness of modules on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A module on an algebraic space is ample as a scheme module when the space is a scheme
and its transport to every representing scheme is ample. -/
def isSchemeAndAmple {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules) : Prop :=
  IsScheme X ∧ ∀ {T : Over S} (e : X ≅ ofOver T),
    Scheme.Modules.isAmpleObject (toSchemeModule e L)

/-- Scheme ampleness is equivalent to representability by a scheme together with ampleness
of the transported module on every representing scheme. -/
theorem isSchemeAndAmple_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (L : X.Modules) :
    isSchemeAndAmple L ↔
      IsScheme X ∧ ∀ {T : Over S} (e : X ≅ ofOver T),
        Scheme.Modules.isAmpleObject (toSchemeModule e L) := by
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
