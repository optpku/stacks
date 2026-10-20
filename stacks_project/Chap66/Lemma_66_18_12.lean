/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.EtaleBaseChange
import StacksCheckRecall

/-! Étale base change of direct images, higher direct images, and inverse images. -/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable (h_cart : IsPullback h f' f g) [AlgebraicSpace.Etale g]

open AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (proof-local temporary data): the certificate in each checked
-- result type is uniquely determined by the pullback square and the étale bottom edge.

/- Lemma 66.18.12: restriction along an étale base change commutes with direct image. -/
@[stacks 03LR] #check
  (AlgebraicGeometry.AlgebraicSpace.isIso_pushforwardEtaleBaseChangeHom h_cart (Type (u + 1)) :
    ∀ F : Sheaf (smallEtaleTopology X) (Type (u + 1)),
      -- Local instance justification (proof-local temporary data): this unique Prop certificate is determined by the cartesian square and its étale bottom edge and is needed to elaborate the comparison map.
      letI : Etale h := Etale.fst_of_isPullback h_cart
      IsIso (pushforwardEtaleBaseChangeHom h_cart (Type (u + 1)) F))

/- Higher direct images of abelian sheaves commute with the same restriction in every degree. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.isIso_higherDirectImageEtaleBaseChangeHom h_cart :
    ∀ (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ),
      -- Local instance justification (proof-local temporary data): this unique Prop certificate is determined by the cartesian square and its étale bottom edge and is needed to elaborate the comparison map.
      letI : Etale h := Etale.fst_of_isPullback h_cart
      IsIso (higherDirectImageEtaleBaseChangeHom h_cart F i))

/- The inverse-image compatibility asserted in the footnote. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.isIso_inverseImageEtaleRestrictHom h_cart :
    ∀ G : Sheaf (smallEtaleTopology Y) (Type (u + 1)),
      -- Local instance justification (proof-local temporary data): this unique Prop certificate is determined by the cartesian square and its étale bottom edge and is needed to elaborate the comparison map.
      letI : Etale h := Etale.fst_of_isPullback h_cart
      IsIso (inverseImageEtaleRestrictHom h_cart (Type (u + 1)) G))
