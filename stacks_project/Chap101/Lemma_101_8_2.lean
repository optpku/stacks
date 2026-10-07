module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Immersions into (locally) Noetherian algebraic stacks

An immersion of algebraic stacks into a locally Noetherian algebraic stack has
locally Noetherian source and is quasi-compact. If the target is Noetherian,
the source is Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom (Immersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.8.2 (1): an immersion of algebraic stacks into a locally
Noetherian algebraic stack has locally Noetherian source. -/
@[stacks 0CPM]
theorem IsLocallyNoetherian.of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (j : X ⟶ Y) [Immersion j]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X :=
  sorry

/-- Lemma 101.8.2 (2): an immersion of algebraic stacks into a locally
Noetherian algebraic stack is quasi-compact. -/
@[stacks 0CPM]
instance QuasiCompact.of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (j : X ⟶ Y) [Immersion j]
    [IsLocallyNoetherian Y] : QuasiCompact j :=
  sorry

/-- Lemma 101.8.2 (3): an immersion of algebraic stacks into a Noetherian
algebraic stack has Noetherian source. -/
@[stacks 0CPM]
theorem IsNoetherian.of_immersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (j : X ⟶ Y) [Immersion j]
    [IsNoetherian Y] : IsNoetherian X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
