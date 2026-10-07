module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap106.Definition_106_3_1_Thickening

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

/-- A thickening of algebraic stacks is representable by an algebraic space if
and only if the target is. -/
theorem isRepresentableByAlgebraicSpace_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsRepresentableByAlgebraicSpace X ↔ IsRepresentableByAlgebraicSpace X' :=
  sorry

/-- A thickening of algebraic stacks is a scheme if and only if the target is,
in the sense of equivalence with the groupoid fibration of a scheme algebraic
space. -/
theorem isScheme_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    (∃ F : AlgebraicSpace S, AlgebraicSpace.IsScheme F ∧ Nonempty (X ≌ F.toGroupoids)) ↔
      (∃ F : AlgebraicSpace S, AlgebraicSpace.IsScheme F ∧ Nonempty (X' ≌ F.toGroupoids)) :=
  sorry

/-- A thickening of algebraic stacks is DM if and only if the target is. -/
theorem isDM_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsDM X ↔ IsDM X' :=
  sorry

/-- A thickening of algebraic stacks is quasi-DM if and only if the target is. -/
theorem isQuasiDM_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsQuasiDM X ↔ IsQuasiDM X' :=
  sorry

/-- A thickening of algebraic stacks is separated if and only if the target is. -/
theorem isSeparated_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsSeparated X ↔ IsSeparated X' :=
  sorry

/-- A thickening of algebraic stacks is quasi-separated if and only if the
target is. -/
theorem isQuasiSeparated_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    IsQuasiSeparated X ↔ IsQuasiSeparated X' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening
