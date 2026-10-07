module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Etale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.13.8: a scheme morphism `f` is étale if and only if it is locally of finite
presentation and the degree `-1` and degree `0` homology objects of its naive cotangent
complex are zero. -/
@[stacks 0G7Z] #check
  (@AlgebraicGeometry.Scheme.Hom.NaiveCotangent.etale_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      Etale f ↔
        LocallyOfFinitePresentation f ∧
          IsZero ((RingedSpace.naiveCotangent f.toShHom).homology (-1)) ∧
            IsZero ((RingedSpace.naiveCotangent f.toShHom).homology 0))
