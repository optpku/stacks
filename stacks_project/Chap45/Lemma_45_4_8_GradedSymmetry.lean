module

public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory

@[expose] public section

open CategoryTheory

universe u

/- Compatibility bridge for the symmetric monoidal structure on graded Chow
correspondences. -/
#check (AlgebraicGeometry.Correspondence.GradedCategory.instSymmetricCategory :
  ∀ {k : Type u} [Field k],
    SymmetricCategory (AlgebraicGeometry.Correspondence.GradedCategory k))
