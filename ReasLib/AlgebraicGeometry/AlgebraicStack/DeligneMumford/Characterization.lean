module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object

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

/-- An algebraic stack is DM if and only if it is Deligne-Mumford if and only if
there exists a scheme with a surjective étale morphism to the stack. -/
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
