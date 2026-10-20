/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Open

/-- A factorization of an open immersion is its scheme-theoretic closure when
it is a scheme-theoretic image factorization of that open immersion. -/
def IsSchemeTheoreticClosure {S : Scheme.{u}} {X U Z : AlgebraicSpace S}
    (j : U ⟶ X) [IsOpenImmersion j] (toClosure : U ⟶ Z) (i : Z ⟶ X) : Prop :=
  IsSchemeTheoreticImage j toClosure i

/-- A factorization of an open immersion is its scheme-theoretic closure if and
only if it is a scheme-theoretic image factorization. -/
theorem isSchemeTheoreticClosure_iff {S : Scheme.{u}} {X U Z : AlgebraicSpace S}
    (j : U ⟶ X) [IsOpenImmersion j] (toClosure : U ⟶ Z) (i : Z ⟶ X) :
    IsSchemeTheoreticClosure j toClosure i ↔ IsSchemeTheoreticImage j toClosure i :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Open
