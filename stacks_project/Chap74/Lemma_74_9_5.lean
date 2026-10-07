module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Definition_67_5_2_Surjective

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 74.9.5 (1): Let `f : X ⟶ Y` be a smooth morphism of algebraic spaces.
If `Y` is reduced, then `X` is reduced. -/
@[stacks 0GB3]
instance isReduced_inheritedFromTarget {S : Scheme.{u}} :
    InheritedFromTarget (@IsReduced S : ObjectProperty (AlgebraicSpace S))
      (@Smooth S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Lemma 74.9.5 (2): Let `f : X ⟶ Y` be a surjective smooth morphism of algebraic
spaces. If `X` is reduced, then `Y` is reduced. -/
@[stacks 0GB3]
instance isReduced_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsReduced S : ObjectProperty (AlgebraicSpace S))
      ((@Smooth S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- If `f : X ⟶ Y` is a smooth morphism of algebraic spaces and `Y` is reduced,
then `X` is reduced. -/
theorem IsReduced.of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] [IsReduced Y] : IsReduced X := sorry

/-- If `f : X ⟶ Y` is a surjective smooth morphism of algebraic spaces and `X` is
reduced, then `Y` is reduced. -/
theorem IsReduced.of_smooth_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] [Surjective f] [IsReduced X] : IsReduced Y := sorry

end AlgebraicGeometry.AlgebraicSpace
