module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Smooth

@[expose] public section

universe u

#check
  (AlgebraicGeometry.AbelianVariety.instSmooth :
    ∀ {k : Type u} [Field k] (A : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A],
      AlgebraicGeometry.Smooth A.hom)
