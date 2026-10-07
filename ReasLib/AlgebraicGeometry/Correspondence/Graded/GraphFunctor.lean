module

public import Mathlib.CategoryTheory.InducedCategory
public import ReasLib.AlgebraicGeometry.Correspondence.Graded.DegreeZero

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.Graded

/-- The category of smooth projective schemes over `k`, with morphisms inherited from
schemes over `k`. -/
abbrev SchemeCategory (k : Type u) [Field k] : Type (u + 1) :=
  InducedCategory (C := Graded k) (SchemeOverField k) scheme

/-- The degree-zero graph correspondence assigned to a morphism in the opposite
category of smooth projective schemes. -/
noncomputable def graphMap {k : Type u} [Field k]
    {X Y : (SchemeCategory k)ᵒᵖ} (f : X ⟶ Y) :
    (⟨X.unop⟩ : DegreeZero (k := k)) ⟶ (⟨Y.unop⟩ : DegreeZero (k := k)) :=
  (degreeZeroHomEquiv ⟨X.unop⟩ ⟨Y.unop⟩).symm
    (Correspondence.rationalGraph f.unop.hom)

/-- Under the degree-zero Hom equivalence, `graphMap f` is the rational Chow class
of the graph of the underlying scheme morphism. -/
theorem graphMap_homogeneous {k : Type u} [Field k]
    {X Y : (SchemeCategory k)ᵒᵖ} (f : X ⟶ Y) :
    degreeZeroHomEquiv (⟨X.unop⟩ : DegreeZero (k := k))
      (⟨Y.unop⟩ : DegreeZero (k := k)) (graphMap f) =
        Correspondence.rationalGraph f.unop.hom := sorry

/-- The graph correspondence assigned to an identity is the identity degree-zero
correspondence. -/
theorem graphMap_id {k : Type u} [Field k] (X : (SchemeCategory k)ᵒᵖ) :
    graphMap (𝟙 X) = 𝟙 (⟨X.unop⟩ : DegreeZero (k := k)) := sorry

/-- Graph correspondences preserve composition in the opposite geometric category. -/
theorem graphMap_comp {k : Type u} [Field k]
    {X Y Z : (SchemeCategory k)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    graphMap (f ≫ g) = graphMap f ≫ graphMap g := sorry

/-- The contravariant graph functor from smooth projective schemes over `k` to
degree-zero rational Chow correspondences. -/
noncomputable def graphFunctor (k : Type u) [Field k] :
    (SchemeCategory k)ᵒᵖ ⥤ DegreeZero (k := k) where
  obj X := ⟨X.unop⟩
  map f := graphMap f
  map_id X := graphMap_id X
  map_comp f g := graphMap_comp f g

/-- The graph functor preserves the underlying smooth projective object. -/
theorem graphFunctor_obj {k : Type u} [Field k] (X : (SchemeCategory k)ᵒᵖ) :
    ((graphFunctor k).obj X).obj = X.unop := sorry

/-- The graph functor maps a geometric morphism to the rational Chow class of its graph. -/
theorem graphFunctor_map {k : Type u} [Field k]
    {X Y : (SchemeCategory k)ᵒᵖ} (f : X ⟶ Y) :
    degreeZeroHomEquiv ((graphFunctor k).obj X) ((graphFunctor k).obj Y)
      ((graphFunctor k).map f) = Correspondence.rationalGraph f.unop.hom := sorry

end AlgebraicGeometry.Correspondence.Graded
