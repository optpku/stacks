/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Completion
public import ReasLib.RingTheory.RegularLocalRing.Flat
public import ReasLib.RingTheory.RegularLocalRing.Completion

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

/-- For a scheme locally of finite type over a Noetherian local ring, regularity of a stalk
after base change to the maximal-ideal completion descends to the stalk at its image. -/
@[stacks 0BG6]
theorem isRegularLocalRing_stalk_of_completionBaseChange
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme := pullback f g
    ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) →
      IsRegularLocalRing (X.presheaf.stalk (pullback.fst f g y)) := sorry

/-- For a scheme locally of finite type over a Noetherian local ring, stalk regularity on the
closed fibre is equivalent to stalk regularity after base change to the maximal-ideal completion. -/
@[stacks 0BG6]
theorem isRegularLocalRing_stalk_iff_completionBaseChange_of_closedFiber
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme := pullback f g
    ∀ y : Y, pullback.snd f g y = closedPoint Ahat →
      (IsRegularLocalRing (Y.presheaf.stalk y) ↔
        IsRegularLocalRing (X.presheaf.stalk (pullback.fst f g y))) := sorry

/-- A proper scheme over a Noetherian local ring is regular if and only if its base change to
the maximal-ideal completion is regular. -/
@[stacks 0BG6]
theorem regular_iff_completionBaseChange_of_isProper
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsProper f] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    let Y : Scheme := pullback f g
    Regular X ↔ Regular Y := sorry

end AlgebraicGeometry.Scheme
