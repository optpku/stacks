module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.AffineProduct
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Products of integral morphisms of schemes

This file records that arbitrary products of integral morphisms over a fixed
base scheme are integral.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over

variable {I : Type u} (S : Scheme.{u})
variable (T : I → CategoryTheory.Over S)

/-- The structure morphism of an arbitrary product of integral morphisms over
a fixed base scheme is integral. -/
instance instIsIntegralHomPiObj [∀ i, IsIntegralHom (T i).hom] :
    IsIntegralHom (piObj T).hom := sorry

end AlgebraicGeometry.Scheme.Over
