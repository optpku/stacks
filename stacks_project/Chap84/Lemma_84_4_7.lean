/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.ProperBaseChange
import StacksCheckRecall

/-!
# Lemma 84.4.7

Proper base change on `D⁺` for algebraic spaces with locally torsion cohomology.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry.AlgebraicSpace

universe u v

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 84.4.7. For a cartesian square of algebraic spaces with proper vertical map,
the canonical derived base-change map is an isomorphism on every bounded-below object
with locally torsion cohomology. -/
@[stacks 0DG3] #check (AlgebraicGeometry.AlgebraicSpace.proper_derivedBaseChange_plus_isIso :
  ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h_cart : IsPullback g' f' f g)
  [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
  [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
  [(smallEtaleInclusion Y').IsCoverDense (spacesEtaleTopology Y')]
  [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
  [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
  [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
  [(sheafPushforwardAbelian f).Additive]
  [(sheafPushforwardAbelian f').Additive]
  [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
  [(sheafPushforwardAbelian f').toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1}))]
  [(sheafInverseImage AddCommGrpCat.{u + 1} g).Additive]
  [(sheafInverseImage AddCommGrpCat.{u + 1} g').Additive]
  (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
  [Proper f],
    DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E →
    IsIso (smallEtaleDerivedBaseChangeHom f g f' g' h_cart E))

#check (AlgebraicGeometry.AlgebraicSpace.proper_derivedBaseChange_plus_isIso_pullback :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
  (f : X ⟶ Y) (g : Y' ⟶ Y)
  [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
  [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
  [(smallEtaleInclusion Y').IsCoverDense (spacesEtaleTopology Y')]
  [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology Y') AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1}]
  [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
  [Abelian (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1})]
  [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology Y') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{v} (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1})]
  [(sheafPushforwardAbelian f).Additive]
  [(sheafPushforwardAbelian (pullback.fst g f)).Additive]
  [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
  [(sheafPushforwardAbelian (pullback.fst g f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (smallEtaleTopology (pullback g f)) AddCommGrpCat.{u + 1}))]
  [(sheafInverseImage AddCommGrpCat.{u + 1} g).Additive]
  [(sheafInverseImage AddCommGrpCat.{u + 1} (pullback.snd g f)).Additive]
  (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
  [Proper f],
    DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E →
    IsIso (smallEtaleDerivedBaseChangeHom_pullback f g E))

end
