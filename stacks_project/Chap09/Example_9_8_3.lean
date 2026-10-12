/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Geometry.Manifold.Complex.FunctionField
import StacksCheckRecall

@[expose] public section

open scoped IntermediateField MeromorphicFunctionField

universe u

variable (X : CompactRiemannSurface.{u}) (f : ℂ(X))

/- Example 9.8.3 (Tag 09GE): for a compact Riemann surface `X` and a nonconstant meromorphic
function `f`, the function field `ℂ(X)` is algebraic over the simple field `ℂ⟮f⟯`. The reusable
function-field bridge is owned by `Geometry.Manifold.Complex.FunctionField`. -/

#check (CompactRiemannSurface.FunctionField.transcendentalOfNotMemRange (X := X) (f := f) :
  f ∉ Set.range (algebraMap ℂ (ℂ(X))) → Transcendental ℂ f)
#check CompactRiemannSurface.FunctionField.existsGenerator X
@[stacks 09GE]
#check (CompactRiemannSurface.FunctionField.isAlgebraicOverAdjoinOfNonconstant X f :
  f ∉ Set.range (algebraMap ℂ (ℂ(X))) → Algebra.IsAlgebraic ℂ⟮f⟯ (ℂ(X)))
