module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

/- Lemma 59.91.6: for a proper morphism `f : X ⟶ Y` of schemes, cohomology
commutes with base change for `f` if and only if, for every prime `ℓ`, every
injective sheaf of `ℤ/ℓℤ`-modules `I` on `X` étale, and every cartesian square
as in `59.91.5.1`, the sheaves `R^q f'_* (g')⁻¹ I` vanish for all `q > 0`. -/
@[stacks 0A4B] #check
  (AlgebraicGeometry.Scheme.Hom.cohomologyCommutesWithBaseChange_iff.{u} :
    ∀ {X Y : Scheme.{u}}
      [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Z : Scheme.{u},
        HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
      (f : X ⟶ Y) [IsProper f],
      CohomologyCommutesWithBaseChange f ↔ injectiveMod_higherDirectImage_isZero f)

end

end
