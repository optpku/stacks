module

public import stacks_project.Chap84.Theorem_84_4_6
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

/-!
# Lemma 84.4.7

Proper base change on `D⁺` for algebraic spaces, when the object has torsion
cohomology sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

section

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion Y').IsCoverDense (spacesEtaleTopology Y')]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).Additive]
variable [(sheafPushforwardAbelian f').Additive]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian f').toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}))]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} g).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} g').Additive]
variable (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))

/-- Lemma 84.4.7: for a cartesian square of algebraic spaces over a scheme `S`
with proper vertical map `f : X ⟶ Y`, and for `E` in `D⁺(X_étale)` with torsion
cohomology sheaves, the canonical derived base-change map
`g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism. -/
@[stacks 0DG3]
theorem proper_derivedBaseChange_plus_isIso [Proper f]
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E) :
    IsIso (smallEtaleDerivedBaseChangeHom f g f' g' h_cart E) :=
  sorry

end

section

variable {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion Y').IsCoverDense (spacesEtaleTopology Y')]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).Additive]
variable [(sheafPushforwardAbelian (pullback.fst g f)).Additive]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian (pullback.fst g f)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1}))]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} g).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (pullback.snd g f)).Additive]
variable (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))

/-- Specialization of `proper_derivedBaseChange_plus_isIso` to the chosen fibre
product `Y' ×_Y X`. -/
theorem proper_derivedBaseChange_plus_isIso_pullback [Proper f]
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E) :
    IsIso (smallEtaleDerivedBaseChangeHom_pullback f g E) :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace
