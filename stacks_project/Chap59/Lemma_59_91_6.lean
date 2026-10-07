module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsProper f]
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.91.6: for a proper morphism `f : X ⟶ Y` of schemes, cohomology
commutes with base change for `f` if and only if, for every prime `ℓ`, every
injective sheaf of `ℤ/ℓℤ`-modules `I` on `X` étale, and every cartesian square
as in `59.91.5.1`, the sheaves `R^q f'_* (g')⁻¹ I` vanish for all `q > 0`. -/
@[stacks 0A4B]
theorem cohomologyCommutesWithBaseChange_iff :
    CohomologyCommutesWithBaseChange f ↔ injectiveMod_higherDirectImage_isZero f := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
