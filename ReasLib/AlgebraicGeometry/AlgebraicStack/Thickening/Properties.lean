/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening

/-!
# Properties invariant under thickenings of algebraic stacks

If `i : X ⟶ X'` is a thickening of algebraic stacks, then `X` and `X'` are
simultaneously an algebraic space, a scheme, DM, quasi-DM, separated, and
quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening

/-- The source of a thickening of algebraic stacks is representable by an
algebraic space if and only if its target is. -/
theorem isRepresentableByAlgebraicSpace_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsRepresentableByAlgebraicSpace X ↔ IsRepresentableByAlgebraicSpace X' :=
  sorry

/-- The source of a thickening of algebraic stacks is a scheme if and only if
its target is, in the sense of equivalence with the groupoid fibration of a
scheme algebraic space. -/
theorem isScheme_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    (∃ F : AlgebraicSpace S, AlgebraicSpace.IsScheme F ∧ Nonempty (X ≌ F.toGroupoids)) ↔
      (∃ F : AlgebraicSpace S, AlgebraicSpace.IsScheme F ∧ Nonempty (X' ≌ F.toGroupoids)) :=
  sorry

/-- The source of a thickening of algebraic stacks is DM if and only if its
target is. -/
theorem isDM_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsDM X ↔ IsDM X' :=
  sorry

/-- The source of a thickening of algebraic stacks is quasi-DM if and only if
its target is. -/
theorem isQuasiDM_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsQuasiDM X ↔ IsQuasiDM X' :=
  sorry

/-- The source of a thickening of algebraic stacks is separated if and only if
its target is. -/
theorem isSeparated_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsSeparated X ↔ IsSeparated X' :=
  sorry

/-- The source of a thickening of algebraic stacks is quasi-separated if and
only if its target is. -/
theorem isQuasiSeparated_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsQuasiSeparated X ↔ IsQuasiSeparated X' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
