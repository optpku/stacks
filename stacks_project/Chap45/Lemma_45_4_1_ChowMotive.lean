module

public import ReasLib.AlgebraicGeometry.ChowMotive.Functor
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Linear

@[expose] public section

open CategoryTheory

universe u

variable (k : Type u) [Field k]

#check
  (ChowMotive.hFunctor k :
    (AlgebraicGeometry.Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤
      ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k))
