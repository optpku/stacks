module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap94.Definition_94_12_2_DeligneMumford
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Characterizations of DM algebraic stacks

An algebraic stack is DM if and only if it is Deligne-Mumford if and only if
it admits a surjective étale morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsDM

/-- Theorem 101.21.6: Let `X` be an algebraic stack. The following are
equivalent: `X` is DM, `X` is Deligne-Mumford, and there exists a scheme `W`
and a surjective étale morphism `W ⟶ X`. -/
@[stacks 06N3]
theorem tfae {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    List.TFAE
      [IsDM X, DeligneMumfordStack X,
        ∃ (W : Over S) (p : GroupoidsOver.slice W ⟶ X),
          Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p] :=
  sorry

/-- An algebraic stack is DM if and only if it is Deligne-Mumford. -/
theorem iff_deligneMumford {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsDM X ↔ DeligneMumfordStack X :=
  sorry

/-- An algebraic stack is DM if and only if there exists a scheme `W` and a
surjective étale morphism `W ⟶ X`. -/
theorem iff_exists_etale_surjective {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsDM X ↔
      ∃ (W : Over S) (p : GroupoidsOver.slice W ⟶ X),
        Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsDM
