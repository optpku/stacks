/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The complement of the image of an open immersion in its target scheme. -/
def closedComplement {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : Set Y :=
  (f.opensRange : Set Y)ᶜ

/-- A scheme morphism is an open immersion exactly when it is isomorphic over its
target to the inclusion of an open subscheme. -/
theorem isOpenImmersion_iff_exists_iso {V X : Scheme.{u}} (f : V ⟶ X) :
    IsOpenImmersion f ↔ ∃ (U : X.Opens) (e : V ≅ U.toScheme), e.hom ≫ U.ι = f := sorry

end AlgebraicGeometry.Scheme.Hom
