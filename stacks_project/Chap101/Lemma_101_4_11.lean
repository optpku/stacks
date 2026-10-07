module

public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Transfer of separation axioms along morphisms of algebraic stacks

If a morphism of algebraic stacks is DM, quasi-DM, separated, or
quasi-separated, then the corresponding relative and absolute separation
axioms pass from the target to the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.4.11 (1): if `Y` is DM over `S` and `f : X ⟶ Y` is DM, then `X`
is DM over `S`. -/
@[stacks 050L]
theorem IsDMOver.of_DM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsDMOver Y] [DM f] :
    IsDMOver X :=
  sorry

/-- Lemma 101.4.11 (2): if `Y` is quasi-DM over `S` and `f : X ⟶ Y` is
quasi-DM, then `X` is quasi-DM over `S`. -/
@[stacks 050L]
theorem IsQuasiDMOver.of_quasiDM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsQuasiDMOver Y]
    [QuasiDM f] : IsQuasiDMOver X :=
  sorry

/-- Lemma 101.4.11 (3): if `Y` is separated over `S` and `f : X ⟶ Y` is
separated, then `X` is separated over `S`. -/
@[stacks 050L]
theorem IsSeparatedOver.of_separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsSeparatedOver Y]
    [Separated f] : IsSeparatedOver X :=
  sorry

/-- Lemma 101.4.11 (4): if `Y` is quasi-separated over `S` and `f : X ⟶ Y` is
quasi-separated, then `X` is quasi-separated over `S`. -/
@[stacks 050L]
theorem IsQuasiSeparatedOver.of_quasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparatedOver Y] [QuasiSeparated f] : IsQuasiSeparatedOver X :=
  sorry

/-- Lemma 101.4.11 (5): if `Y` is DM and `f : X ⟶ Y` is DM, then `X` is DM. -/
@[stacks 050L]
theorem IsDM.of_DM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsDM Y] [DM f] :
    IsDM X :=
  sorry

/-- Lemma 101.4.11 (6): if `Y` is quasi-DM and `f : X ⟶ Y` is quasi-DM, then
`X` is quasi-DM. -/
@[stacks 050L]
theorem IsQuasiDM.of_quasiDM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsQuasiDM Y]
    [QuasiDM f] : IsQuasiDM X :=
  sorry

/-- Lemma 101.4.11 (7): if `Y` is separated and `f : X ⟶ Y` is separated, then
`X` is separated. -/
@[stacks 050L]
theorem IsSeparated.of_separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsSeparated Y]
    [Separated f] : IsSeparated X :=
  sorry

/-- Lemma 101.4.11 (8): if `Y` is quasi-separated and `f : X ⟶ Y` is
quasi-separated, then `X` is quasi-separated. -/
@[stacks 050L]
theorem IsQuasiSeparated.of_quasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparated Y] [QuasiSeparated f] : IsQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
