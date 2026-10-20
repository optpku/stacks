/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Regular.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.11.2 (1): regularity of a stalk on the maximal-ideal-completion base
change descends to the stalk at its image. -/
@[stacks 0BG6] #check (AlgebraicGeometry.Scheme.isRegularLocalRing_stalk_of_completionBaseChange :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f],
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme := pullback f g
    ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) →
      IsRegularLocalRing (X.presheaf.stalk (pullback.fst f g y)))

/- Lemma 54.11.2 (2): on the closed fibre, stalk regularity is equivalent across
the maximal-ideal-completion base change. -/
@[stacks 0BG6] #check
  (AlgebraicGeometry.Scheme.isRegularLocalRing_stalk_iff_completionBaseChange_of_closedFiber :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f],
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme := pullback f g
    ∀ y : Y, pullback.snd f g y = closedPoint Ahat →
      (IsRegularLocalRing (Y.presheaf.stalk y) ↔
        IsRegularLocalRing (X.presheaf.stalk (pullback.fst f g y))))

/- Lemma 54.11.2 (3): for a proper scheme over a Noetherian local ring,
regularity is equivalent to regularity after base change to the maximal-ideal completion. -/
@[stacks 0BG6] #check (AlgebraicGeometry.Scheme.regular_iff_completionBaseChange_of_isProper :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f],
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme := pullback f g
    Regular X ↔ Regular Y)

end AlgebraicGeometry.Scheme
