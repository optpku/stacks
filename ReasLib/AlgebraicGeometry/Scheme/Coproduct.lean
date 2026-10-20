module

public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical morphisms for coproducts of schemes
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Coproduct

/-- Every canonical summand injection into a coproduct of schemes is an open immersion. -/
@[stacks 03DP "coproduct summand inclusion"]
instance sigma_ι_isOpenImmersion {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) (i : ι) : IsOpenImmersion (Sigma.ι X i) := sorry

end AlgebraicGeometry.Scheme.Coproduct
