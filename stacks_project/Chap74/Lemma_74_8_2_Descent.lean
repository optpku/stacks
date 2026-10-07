module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Descent of finiteness along fppf morphisms

If `f` is a surjective, flat, and locally of finite presentation morphism of
algebraic spaces, and `f ≫ q` is locally of finite presentation (resp. locally
of finite type), then `q` has the same property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFinitePresentation

/-- Local finite presentation of morphisms of algebraic spaces descends under
precomposition by a surjective, flat, locally of finite presentation
morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`, local
finite presentation descends from `p` to `q` when `f` is surjective, flat, and
locally of finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation p] (hcomm : f ≫ q = p) :
    LocallyOfFinitePresentation q := sorry

end LocallyOfFinitePresentation

namespace LocallyOfFiniteType

/-- Local finite type of morphisms of algebraic spaces descends under
precomposition by a surjective, flat, locally of finite presentation
morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`, local
finite type descends from `p` to `q` when `f` is surjective, flat, and locally
of finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType p] (hcomm : f ≫ q = p) :
    LocallyOfFiniteType q := sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
