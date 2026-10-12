/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 74.9.3: If `f : X ⟶ Y` is a morphism of algebraic spaces that is locally
of finite presentation, flat, and surjective, and `X` is locally Noetherian, then
`Y` is locally Noetherian. -/
@[stacks 06MJ]
instance isLocallyNoetherian_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsLocallyNoetherian S : ObjectProperty (AlgebraicSpace S))
      ((@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- If `f : X ⟶ Y` is locally of finite presentation, flat, and surjective, and
`X` is locally Noetherian, then `Y` is locally Noetherian. -/
theorem IsLocallyNoetherian.of_locallyOfFinitePresentation_flat_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Surjective f] [IsLocallyNoetherian X] :
    IsLocallyNoetherian Y := sorry

end AlgebraicGeometry.AlgebraicSpace
