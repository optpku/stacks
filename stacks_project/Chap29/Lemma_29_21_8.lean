module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.21.8 (1): a morphism which is locally of finite presentation is locally of finite type. -/
@[stacks 01TW] #check
  (AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f], LocallyOfFiniteType f)

/- Lemma 29.21.8 (2): a morphism of finite presentation is of finite type. -/
@[stacks 01TW] #check
  (AlgebraicGeometry.Scheme.Hom.instFiniteTypeOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f], Scheme.Hom.FiniteType f)
