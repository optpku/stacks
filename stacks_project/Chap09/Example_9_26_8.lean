module

public import ReasLib.Geometry.Manifold.Complex.FunctionField
import StacksCheckRecall

@[expose] public section

open scoped IntermediateField Manifold MeromorphicFunctionField

universe u

variable (X Y : CompactRiemannSurface.{u})

/- Example 9.26.8 (Tag 09IB): the meromorphic function field of a compact Riemann surface has
transcendence degree one over `ℂ`; conversely, every essentially finite type extension of `ℂ` of
transcendence degree one is realized by such a surface, with isomorphisms corresponding
contravariantly. -/

@[stacks 09IB]
#check (CompactRiemannSurface.functionField_trdeg_eq_one X : Algebra.trdeg ℂ (ℂ(X)) = 1)
#check CompactRiemannSurface.existsWithFunctionFieldOfEssFiniteTypeTrdegEqOne
#check (CompactRiemannSurface.nonemptyIsoIffNonemptyFunctionFieldAlgEquiv X Y :
  Nonempty (X ≅ Y) ↔ Nonempty (ℂ(Y) ≃ₐ[ℂ] ℂ(X)))
