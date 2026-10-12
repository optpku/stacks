/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Basis.SectionFamilies
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable {BX : Set (Opens X)} {BY : Set (Opens Y)}

/- Lemma 6.30.17: a compatible family of `𝒪_Y(V)`-linear maps `𝒢(V) ⟶ ℱ(U)` for basis
opens `V ∈ BY`, `U ∈ BX`, and `U ⊆ f⁻¹(V)` comes from a unique morphism of sheaves of
`𝒪_Y`-modules `𝒢 ⟶ f_* ℱ`, whose restriction from `f⁻¹(V)` to `U` recovers the given map. -/
@[stacks 009Y]
#check
  RingedSpace.Module.BasisPushforwardHomFamily.existsUniquePushforwardHom
    f

/- Companion API: for downstream constructions, the shared owner packages existence, uniqueness,
and restriction into a reversible equivalence with linear two-basis families. -/
#check RingedSpace.Module.BasisPushforwardHomFamily.homEquiv f

end AlgebraicGeometry
