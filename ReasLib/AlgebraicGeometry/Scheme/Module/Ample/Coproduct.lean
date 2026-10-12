/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Ample invertible modules on finite coproducts

A finite coproduct of schemes admitting ample invertible modules again admits an ample
invertible module.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite coproduct of schemes admitting ample invertible modules admits an ample invertible
module. -/
theorem hasAmpleInvertibleModule_sigma {ι : Type u} [Finite ι] (X : ι → Scheme.{u})
    (hX : ∀ i, HasAmpleInvertibleModule (X i)) :
    HasAmpleInvertibleModule (∐ X) := sorry

end AlgebraicGeometry.Scheme.Modules
