module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.56.3: a quasi-finite morphism between affine schemes factors through an affine scheme
as an open immersion followed by a finite morphism. -/
@[stacks 03GU] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affine_openImmersion_finiteFactorization :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y]
      [AlgebraicGeometry.Scheme.Hom.QuasiFinite f],
      ∃ (Z : AlgebraicGeometry.Scheme.{u}) (j : Y ⟶ Z) (π : Z ⟶ X),
        AlgebraicGeometry.IsAffine Z ∧ AlgebraicGeometry.IsOpenImmersion j ∧
          AlgebraicGeometry.IsFinite π ∧ j ≫ π = f)
