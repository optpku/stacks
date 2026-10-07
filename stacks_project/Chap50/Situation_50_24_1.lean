module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperSmoothFamily

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Situation 50.24.1: `S` is quasi-compact and quasi-separated, and `f : X ⟶ S`
is proper and smooth with nonempty equidimensional fibres of dimension `n`. -/
@[stacks 0G8G] #check
  (AlgebraicGeometry.Scheme.Hom.isProperSmoothFamily_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ),
      AlgebraicGeometry.Scheme.Hom.IsProperSmoothFamily f n ↔
        CompactSpace S ∧ QuasiSeparatedSpace S ∧ IsProper f ∧ Smooth f ∧
          AlgebraicGeometry.Scheme.Hom.RelativeDimension f n ∧
            ∀ s : S, Nonempty (f.fiber s))
