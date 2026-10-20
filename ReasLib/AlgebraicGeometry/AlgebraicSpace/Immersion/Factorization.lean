/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Factorizations of immersions of algebraic spaces

An immersion of algebraic spaces over a scheme factors as a closed immersion
followed by an open immersion. A quasi-compact immersion also factors as an
open immersion followed by a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsImmersion

/-- An immersion of algebraic spaces over a scheme factors as a closed immersion
followed by an open immersion. -/
@[stacks 04CE]
theorem exists_closedImmersion_openImmersion_factorization {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f] :
    ∃ (U : AlgebraicSpace S) (c : Z ⟶ U) (o : U ⟶ X),
      IsClosedImmersion c ∧ IsOpenImmersion o ∧ c ≫ o = f :=
  sorry

/-- A morphism of algebraic spaces is an immersion if and only if it factors as
a closed immersion followed by an open immersion. -/
theorem iff_exists {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) :
    IsImmersion f ↔
      ∃ (U : AlgebraicSpace S) (c : Z ⟶ U) (o : U ⟶ X),
        IsClosedImmersion c ∧ IsOpenImmersion o ∧ c ≫ o = f :=
  sorry

/-- A quasi-compact immersion of algebraic spaces over a scheme factors as an
open immersion followed by a closed immersion. -/
@[stacks 081U]
theorem exists_openImmersion_closedImmersion_factorization {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f] [QuasiCompact f] :
    ∃ (Zbar : AlgebraicSpace S) (j : Z ⟶ Zbar) (i : Zbar ⟶ X),
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = f :=
  sorry

/-- A quasi-compact morphism of algebraic spaces is an immersion if and only if
it factors as an open immersion followed by a closed immersion. -/
theorem iff_exists_of_quasiCompact {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [QuasiCompact f] :
    IsImmersion f ↔
      ∃ (Zbar : AlgebraicSpace S) (j : Z ⟶ Zbar) (i : Zbar ⟶ X),
        IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = f :=
  sorry

end IsImmersion

end AlgebraicGeometry.AlgebraicSpace
