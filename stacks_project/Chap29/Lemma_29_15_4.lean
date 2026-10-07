module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory Limits

universe u

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/- Lemma 29.15.4 (1): the base change of a morphism which is locally of finite type is locally of
finite type. -/
@[stacks 01T4] #check
  (MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) f g :
    LocallyOfFiniteType f → LocallyOfFiniteType (pullback.snd f g))

end

/- Lemma 29.15.4 (2): the base change of a morphism of finite type is of finite type. -/
@[stacks 01T4] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.pullback_snd :
    ∀ {X S S' : Scheme.{u}} {f : X ⟶ S},
      Scheme.Hom.FiniteType f → ∀ g : S' ⟶ S, Scheme.Hom.FiniteType (pullback.snd f g))
