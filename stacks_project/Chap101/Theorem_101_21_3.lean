module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiDM.SchemeCover
import StacksCheckRecall

/-!
# Quasi-DM algebraic stacks via locally quasi-finite flat scheme covers

An algebraic stack is quasi-DM if and only if it admits a surjective, flat,
locally finitely presented, locally quasi-finite morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Theorem 101.21.3: Let `X` be an algebraic stack. The following are
equivalent: `X` is quasi-DM, and there exists a scheme `W` and a surjective,
flat, locally finitely presented, locally quasi-finite morphism `W ⟶ X`. -/
@[stacks 06MF] #check
  (AlgebraicGeometry.AlgebraicStack.isQuasiDM_iff_existsLocallyQuasiFiniteFlatCover :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsQuasiDM X ↔
        ∃ (W : Over S) (f : GroupoidsOver.slice W ⟶ X),
          Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f ∧
            Groupoids.Hom.LocallyOfFinitePresentation f ∧
            Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f)
