module

public import ReasLib.AlgebraicGeometry.Correspondence.Monoidal

@[expose] public section

open CategoryTheory

universe u

/- Compatibility bridge for the symmetric monoidal structure on rational Chow
correspondences. -/
#check (AlgebraicGeometry.Correspondence.instSymmetricCategory :
  ∀ {k : Type u} [Field k],
    SymmetricCategory (AlgebraicGeometry.Correspondence.Category k))
