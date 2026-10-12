/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Cancellation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective

/-!
# Cancellation for quasi-projective morphisms

This file records when quasi-projectivity of a composite descends to its first morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.QuasiProjective

/-- A quasi-compact morphism is quasi-projective when its composite with another morphism is
quasi-projective. -/
theorem of_comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} [QuasiCompact f]
    (hfg : QuasiProjective (f ≫ g)) : QuasiProjective f := sorry

end AlgebraicGeometry.QuasiProjective
