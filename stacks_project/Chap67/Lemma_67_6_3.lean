module

public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen

/-!
# Base change of universally open morphisms of algebraic spaces

The base change of a universally open morphism of algebraic spaces by any
morphism of algebraic spaces is universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universally open morphisms of algebraic spaces are stable under base change. -/
instance universallyOpen_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) := sorry

#check UniversallyOpen.of_isPullback

/-- Lemma 67.6.3: The base change of a universally open morphism of algebraic
spaces by any morphism of algebraic spaces is universally open. -/
@[stacks 03Z3]
theorem universallyOpen_baseChange {S : Scheme.{u}}
    {X Y Z P : AlgebraicSpace S} {f : X ⟶ Y} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    (hf : UniversallyOpen f) (h : IsPullback pZ pX g f) :
    UniversallyOpen pZ := sorry

end AlgebraicGeometry.AlgebraicSpace
