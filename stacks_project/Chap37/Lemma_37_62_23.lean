/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Conormal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormallyUnramified

open Scheme.Hom.Conormal.Transitivity

variable {X Y Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Y).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})]

/- Lemma 37.62.23: for formally unramified morphisms `i : Z ⟶ Y` and `j : Y ⟶ X`,
if `i` is a local complete intersection morphism, then the canonical conormal transitivity
complex is short exact. -/
@[stacks 06BA] #check
  (AlgebraicGeometry.FormallyUnramified.conormalTransitivity_shortExact_of_localCompleteIntersection :
    ∀ (i : Z ⟶ Y) (j : Y ⟶ X) [FormallyUnramified i] [FormallyUnramified j]
      [LocallyOfType RingHom.IsLocalCompleteIntersection i],
      (complex i j).ShortExact)

end AlgebraicGeometry.FormallyUnramified
