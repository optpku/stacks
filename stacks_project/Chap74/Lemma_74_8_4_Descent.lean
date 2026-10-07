module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Descent of smoothness and étaleness along fppf morphisms

If `f` is a surjective, flat, and locally of finite presentation morphism of
algebraic spaces, and `f ≫ q` is smooth (resp. étale), then `q` is smooth
(resp. étale).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Smooth

/-- Smoothness of morphisms of algebraic spaces descends under precomposition by
a surjective, flat, locally of finite presentation morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Smooth S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
smoothness descends from `p` to `q` when `f` is surjective, flat, and locally of
finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Smooth p]
    (hcomm : f ≫ q = p) : Smooth q := sorry

end Smooth

namespace Etale

/-- Étaleness of morphisms of algebraic spaces descends under precomposition by
a surjective, flat, locally of finite presentation morphism. -/
instance hasOfPrecompFppf {S : Scheme.{u}} :
    MorphismProperty.HasOfPrecompProperty
      (@Etale S : MorphismProperty (AlgebraicSpace S))
      ((@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S) :
        MorphismProperty (AlgebraicSpace S)) := sorry

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
étaleness descends from `p` to `q` when `f` is surjective, flat, and locally of
finite presentation. -/
theorem of_comp_eq_of_fppf {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Etale p]
    (hcomm : f ≫ q = p) : Etale q := sorry

end Etale

end AlgebraicGeometry.AlgebraicSpace
