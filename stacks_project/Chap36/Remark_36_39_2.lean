module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Remark 36.39.2: derived pullback preserves perfect objects of Tor-amplitude in `[-1, 0]`
and admits compatible determinant constructions, including the determinant-line comparison,
rank-zero preservation, and compatibility of canonical sections. -/
@[stacks 0FJY] #check
  (AlgebraicGeometry.Scheme.PerfectDerived.TorNegOneZero.Determinant.Pullback.nonempty :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}
      [DerivedCategory.DerivedTensor.Right.Has
        (C := AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)]
      [DerivedCategory.DerivedTensor.Right.Has
        (C := AlgebraicGeometry.RingedSpace.Modules Y.toRingedSpace)] (f : X ⟶ Y),
      Nonempty
        (AlgebraicGeometry.Scheme.PerfectDerived.TorNegOneZero.Determinant.Pullback f))
