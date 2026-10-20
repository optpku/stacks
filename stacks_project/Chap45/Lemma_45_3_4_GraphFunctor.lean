module

public import ReasLib.AlgebraicGeometry.Correspondence.Graded.GraphFunctor

open CategoryTheory

universe u

#check (@AlgebraicGeometry.Correspondence.Graded.graphFunctor :
  (k : Type u) → [Field k] →
    (AlgebraicGeometry.Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤
      AlgebraicGeometry.Correspondence.Graded.DegreeZero (k := k))
