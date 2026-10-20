module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.Points
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

/- 97.13.0.1: For every scheme, points of the universal coefficient spectrum
classify free distinguished algebras over its global sections. -/
@[stacks 05YM] #check (UniversalFiniteFreeAlgebra.schemeHomEquiv :
  (T : Scheme.{0}) → (d : ℕ+) →
    (T ⟶ UniversalFiniteFreeAlgebra.baseScheme d) ≃ FreeDimAlgebra Γ(T, ⊤) d)
