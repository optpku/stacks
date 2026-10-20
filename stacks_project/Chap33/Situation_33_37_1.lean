/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair.Pullback

@[expose] public section

universe u

/- Situation 33.37.1: for two subrings of a field having that field as their
fraction field, their intersection is the pullback of their inclusions. -/
@[stacks 09MY] #check
  (FractionRing.SubringPair.intersectionEquivPullback :
    ∀ {K : Type u} [Field K] (P : FractionRing.SubringPair K),
      P.intersection ≃+* RingHom.pullback P.left.subtype P.right.subtype)

/- The source data is an ordered pair of subrings with a common ambient
fraction field. -/
#check (FractionRing.SubringPair : ∀ (K : Type u) [Field K], Type u)

/- Such a pair is constructed from the two subrings and their fraction-field
structures. -/
#check
  (FractionRing.SubringPair.ofSubrings :
    ∀ {K : Type u} [Field K] (left right : Subring K),
      @IsFractionRing left _ K _ left.subtype.toAlgebra →
      @IsFractionRing right _ K _ right.subtype.toAlgebra →
      FractionRing.SubringPair K)

/- The ring in the lower-left corner is the intersection of the two
components. -/
#check
  (FractionRing.SubringPair.intersection :
    ∀ {K : Type u} [Field K] (P : FractionRing.SubringPair K), Subring K)

/- The left leg of the diagram is the canonical inclusion. -/
#check
  (FractionRing.SubringPair.toLeft :
    ∀ {K : Type u} [Field K] (P : FractionRing.SubringPair K),
      P.intersection →+* P.left)

/- The right leg of the diagram is the canonical inclusion. -/
#check
  (FractionRing.SubringPair.toRight :
    ∀ {K : Type u} [Field K] (P : FractionRing.SubringPair K),
      P.intersection →+* P.right)
