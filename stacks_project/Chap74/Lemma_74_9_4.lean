module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 74.9.4: If `f : X ⟶ Y` is a morphism of algebraic spaces that is locally
of finite presentation, flat, and surjective, and `X` is regular, then
`Y` is regular. -/
@[stacks 06MK]
instance isRegular_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsRegular S : ObjectProperty (AlgebraicSpace S))
      ((@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- If `f : X ⟶ Y` is locally of finite presentation, flat, and surjective, and
`X` is regular, then `Y` is regular. -/
theorem IsRegular.of_locallyOfFinitePresentation_flat_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Surjective f] [IsRegular X] :
    IsRegular Y := sorry

end AlgebraicGeometry.AlgebraicSpace
