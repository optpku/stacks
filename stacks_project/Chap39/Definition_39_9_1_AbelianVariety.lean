module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety

universe u

#check (AlgebraicGeometry.AbelianVariety :
  ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
    [CategoryTheory.GrpObj G], Prop)
