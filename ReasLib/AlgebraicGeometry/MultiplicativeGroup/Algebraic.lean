module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The multiplicative group over a field is algebraic. -/
instance instAlgebraic_multiplicativeGroupOverField (k : Type u) [Field k] :
    Algebraic (𝔾ₘ[Spec (.of k)]).toGrp.X :=
  sorry

end AlgebraicGeometry
