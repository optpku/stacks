/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Theorem_84_4_6_Comparison

/-!
# Theorem 84.4.6

Proper base change for abelian torsion sheaves on the small étale site of an
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

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
variable (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

/-- Theorem 84.4.6: if `f : X ⟶ Y` is a proper morphism of algebraic spaces over a
scheme `S` and `g : Y' ⟶ Y` is any morphism, with cartesian projections
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`, then for any abelian torsion sheaf `F` on
`X_étale` the derived comparison `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` is an
isomorphism. -/
@[stacks 0DG2]
theorem proper_derivedBaseChange_isIso [Proper f] (hF : IsLocallyTorsion F) :
    IsIso
      (smallEtaleDerivedBaseChangeHom f g f' g' h_cart
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) 0).obj F)) :=
  sorry

/-- Unpacking of Theorem 84.4.6 at cohomology sheaves: the named degree-`q`
comparison `higherDirectImage_baseChangeHom` is an isomorphism for every
locally torsion abelian étale sheaf. -/
theorem proper_higherDirectImage_baseChangeHom_isIso [Proper f]
    (hF : IsLocallyTorsion F) (q : ℕ) :
    IsIso (higherDirectImage_baseChangeHom f g f' g' h_cart F q) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
