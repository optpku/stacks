module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.15.5 (1): a closed immersion is of finite type. -/
@[stacks 01T5] #check
  (@AlgebraicGeometry.Scheme.Hom.instFiniteTypeOfIsClosedImmersion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f], Scheme.Hom.FiniteType f)

/- Lemma 29.15.5 (2): an immersion is locally of finite type. -/
@[stacks 01T5] #check
  (@AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f], LocallyOfFiniteType f)
