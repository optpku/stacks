/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Étale algebraic spaces over a field

An algebraic space étale over the spectrum of a field is representable by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- An algebraic space étale over the spectrum of a field over a base scheme is
representable by a scheme over that base. -/
theorem of_etale_over_field {S : Scheme.{u}} {k : Type u} [Field k] {X : AlgebraicSpace S}
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : X ⟶ ofOver (Over.mk σ)) [Etale f] :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
