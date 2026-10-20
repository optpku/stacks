module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AbelianBaseChange
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

/-!
# Proper derived base change for algebraic spaces

Proper base change for locally torsion abelian sheaves and bounded-below complexes
with locally torsion cohomology on the small étale site of an algebraic space.
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
variable (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

/-- If `f : X ⟶ Y` is a proper morphism of algebraic spaces over a
scheme `S` and `g : Y' ⟶ Y` is any morphism, with cartesian projections
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`, then for any locally torsion abelian sheaf `F` on
`X_étale` the derived comparison `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` is an
isomorphism. -/
@[stacks 0DG2]
theorem proper_derivedBaseChange_isIso [Proper f] (hF : IsLocallyTorsion F) :
    IsIso
      (smallEtaleDerivedBaseChangeHom f g f' g' h_cart
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) 0).obj F)) :=
  sorry

/-- For a proper morphism and a locally torsion abelian étale sheaf, every degreewise
right derivative of the underived base-change mate between the composite functors
`f_* ⋙ g⁻¹` and `(g')⁻¹ ⋙ f'_*` is an isomorphism. -/
theorem proper_higherDirectImage_baseChangeHom_isIso [Proper f]
    (hF : IsLocallyTorsion F) (q : ℕ) :
    IsIso (higherDirectImage_baseChangeHom f g f' g' h_cart F q) :=
  sorry

/-- Proper derived base change is invertible when the cartesian-square and local-torsion
hypotheses are supplied as facts. -/
instance proper_derivedBaseChange_isIso_of_fact [Proper f]
    [hCart : Fact (IsPullback g' f' f g)] [hF : Fact (IsLocallyTorsion F)] :
    IsIso
      (smallEtaleDerivedBaseChangeHom f g f' g' hCart.out
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) 0).obj F)) :=
  proper_derivedBaseChange_isIso f g f' g' hCart.out F hF.out

/-- The degreewise right derivative of the underived base-change mate for a proper morphism
is invertible when the cartesian-square and local-torsion hypotheses are supplied as facts. -/
instance proper_higherDirectImage_baseChangeHom_isIso_of_fact [Proper f]
    [hCart : Fact (IsPullback g' f' f g)] [hF : Fact (IsLocallyTorsion F)] (q : ℕ) :
    IsIso (higherDirectImage_baseChangeHom f g f' g' hCart.out F q) :=
  proper_higherDirectImage_baseChangeHom_isIso f g f' g' hCart.out F hF.out q

end

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

/-- For a cartesian square of algebraic spaces over a scheme `S`
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

/-- Proper derived base change on a bounded-below object is invertible when the cartesian
square and locally torsion cohomology hypotheses are supplied as facts. -/
instance proper_derivedBaseChange_plus_isIso_of_fact [Proper f]
    [hCart : Fact (IsPullback g' f' f g)]
    [hE : Fact (DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E)] :
    IsIso (smallEtaleDerivedBaseChangeHom f g f' g' hCart.out E) :=
  proper_derivedBaseChange_plus_isIso f g f' g' hCart.out E hE.out

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

/-- For a proper morphism of algebraic spaces and a bounded-below derived object with
locally torsion cohomology, the canonical derived comparison for the chosen fibre product
`Y' ×_Y X` is an isomorphism. -/
theorem proper_derivedBaseChange_plus_isIso_pullback [Proper f]
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E) :
    IsIso (smallEtaleDerivedBaseChangeHom_pullback f g E) :=
  sorry

/-- Proper derived base change for the chosen fibre product is invertible on a bounded-below
object when locally torsion cohomology is supplied as a fact. -/
instance proper_derivedBaseChange_plus_isIso_pullback_of_fact [Proper f]
    [hE : Fact (DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E)] :
    IsIso (smallEtaleDerivedBaseChangeHom_pullback f g E) :=
  proper_derivedBaseChange_plus_isIso_pullback f g E hE.out

end

end AlgebraicGeometry.AlgebraicSpace
