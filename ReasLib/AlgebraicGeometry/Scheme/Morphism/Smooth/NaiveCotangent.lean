module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.AffineComparison.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Smooth

/-- A scheme morphism is smooth exactly when it is locally of finite presentation, its degree
`-1` naive-cotangent homology is zero, and its relative differentials are finite locally free. -/
@[stacks 0D0N]
theorem iff_naiveCotangent {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Smooth f ↔
      LocallyOfFinitePresentation f ∧
        IsZero ((NL[f.toShHom]).homology (-1)) ∧
          (Ω[f.toShHom]).IsFiniteLocallyFree := sorry

end AlgebraicGeometry.Smooth
