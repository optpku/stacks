module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- A scheme morphism is étale if and only if it is locally of finite presentation and the
homology objects in degrees `-1` and `0` of its naive cotangent complex vanish. -/
@[stacks 0G7Z]
theorem etale_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale f ↔
      LocallyOfFinitePresentation f ∧
        IsZero ((RingedSpace.naiveCotangent f.toShHom).homology (-1)) ∧
          IsZero ((RingedSpace.naiveCotangent f.toShHom).homology 0) := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
