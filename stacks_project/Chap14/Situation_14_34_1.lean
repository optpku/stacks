/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCheckRecall

/-!
@stack 08N9

# Source-facing recall for Situation 14.34.1

The situation fixes two functors together with a specified adjunction; the canonical mathlib
owner is `CategoryTheory.Adjunction`.
-/

@[expose] public section

universe uA uS vA vS

namespace CategoryTheory

variable {𝒜 : Type uA} {𝒮 : Type uS} [Category.{vA} 𝒜] [Category.{vS} 𝒮]
variable (U : 𝒮 ⥤ 𝒜) (V : 𝒜 ⥤ 𝒮)
variable (adj : U ⊣ V)

/- Situation 14.34.1: categories `𝒜` and `𝒮`, a functor
`V : 𝒜 ⥤ 𝒮`, and a specified left adjoint `U : 𝒮 ⥤ 𝒜`;
this setup is expressed by fixing an adjunction witness `adj : U ⊣ V`. -/
@[stacks 08N9 "Situation 14.34.1"]
#check (adj : U ⊣ V)

end CategoryTheory
