module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.Composition
import StacksCheckRecall

/-!
# Composition of finite presentation morphisms of algebraic spaces

The composition of a pair of finite presentation morphisms of algebraic spaces
is of finite presentation, and the same holds for morphisms locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.28.2 (1): The composition of finite presentation morphisms of
algebraic spaces is of finite presentation. -/
@[stacks 03XQ] #check
  (AlgebraicGeometry.AlgebraicSpace.finitePresentation_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.finitePresentation_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    [FinitePresentation f] → [FinitePresentation g] → FinitePresentation (f ≫ g))

/- Lemma 67.28.2 (2): The composition of locally of finite presentation
morphisms of algebraic spaces is locally of finite presentation. -/
@[stacks 03XQ] #check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_isStableUnderComposition :
  ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
    (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    [LocallyOfFinitePresentation f] → [LocallyOfFinitePresentation g] →
      LocallyOfFinitePresentation (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
