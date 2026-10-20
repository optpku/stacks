module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
import StacksCheckRecall

universe u

/- Lemma 67.23.2. The composition of finite type morphisms of algebraic spaces is of finite
type. The same holds for locally of finite type. -/
@[stacks 03XG] #check
  (AlgebraicGeometry.AlgebraicSpace.finiteType_isStableUnderComposition :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      CategoryTheory.MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.AlgebraicSpace.FiniteType S :
          CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))

-- The composition of locally of finite type morphisms is locally of finite type.
#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_isStableUnderComposition :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType S :
        CategoryTheory.MorphismProperty (AlgebraicGeometry.AlgebraicSpace S)))
