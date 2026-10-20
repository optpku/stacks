module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace.Immersion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 110.29.1: there exists a finite type morphism of algebraic spaces
`Y ⟶ X` with `Y` affine and `X` quasi-separated such that there does not exist
an immersion `Y ⟶ AffineSpace (ULift (Fin n)) X` over `X`. -/
@[stacks 088W] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_finiteType_without_immersion_to_affineSpace.{u} :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsAffine Y ∧ FiniteType f ∧ IsAbsolutelyQuasiSeparated X ∧
        ¬ existsImmersionToAffineSpace f)
