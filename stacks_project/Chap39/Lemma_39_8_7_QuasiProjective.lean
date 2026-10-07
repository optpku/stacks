module

public import ReasLib.AlgebraicGeometry.GroupScheme.QuasiProjective

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

#check
  (AlgebraicGeometry.GroupScheme.instQuasiProjective :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] [Algebraic G],
      QuasiProjective G.hom)
