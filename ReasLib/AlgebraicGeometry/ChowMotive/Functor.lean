module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.Correspondence.Graded.GraphFunctor
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Linear

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents

noncomputable section

universe u

namespace ChowMotive

open AlgebraicGeometry
open AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The contravariant graph functor from smooth projective schemes to Chow motives. -/
def hFunctor (k : Type u) [Field k] :
    (Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤
      ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) :=
  Correspondence.Graded.graphFunctor k ⋙
    Correspondence.Graded.zeroTwistFunctor k ⋙
      toKaroubi (Correspondence.GradedCategory k)

/-- On objects, the graph functor lands on the identity-projector motive in Tate twist zero. -/
theorem hFunctor_obj (X : (Correspondence.Graded.SchemeCategory k)ᵒᵖ) :
    (hFunctor k).obj X =
      (toKaroubi (Correspondence.GradedCategory k)).obj
        (Correspondence.GradedCategory.ofScheme X.unop.scheme 0) := sorry

/-- On morphisms, the underlying correspondence of the graph functor is the rational graph class. -/
theorem hFunctor_map_graph {X Y : (Correspondence.Graded.SchemeCategory k)ᵒᵖ}
    (f : X ⟶ Y) :
    ((hFunctor k).map f).f = Correspondence.rationalGraph f.unop.hom := sorry

end ChowMotive
