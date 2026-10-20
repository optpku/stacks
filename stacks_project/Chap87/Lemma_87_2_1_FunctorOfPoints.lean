module

public import ReasLib.AlgebraicGeometry.FormalScheme.FunctorOfPoints

/-!
# Functor of points of a formal scheme

The functor of points is Yoneda restricted along the scheme comparison.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.FormalScheme

/- Lemma 87.2.1. The restricted functor of points. -/
#check (AlgebraicGeometry.FormalScheme.functorOfPoints :
    (P : ObjectProperty Scheme.{u}) →
      FormalScheme.{u} ⥤ (P.FullSubcategory)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.FormalScheme.functorOfPoints_obj :
    ∀ (P : ObjectProperty Scheme.{u}) (X : FormalScheme.{u})
      (S : (P.FullSubcategory)ᵒᵖ),
      ((functorOfPoints P).obj X).obj S =
        (Scheme.toFormalScheme.obj (P.ι.obj S.unop) ⟶ X))

end AlgebraicGeometry.FormalScheme
