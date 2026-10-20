/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.RingTheory.AdicCompletion.LocalMap

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

/-- Base change to the maximal-ideal-adic completion preserves completed stalks
at points lying over the closed point of the base. -/
@[stacks 0BG5]
theorem completionStalkMap_bijective_of_baseChange
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hfg : (maximalIdeal A).FG) (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) :
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    ∀ q : (pullback f g : Scheme),
      f (pullback.fst f g q) = closedPoint A →
        Function.Bijective
          (AdicCompletion.mapLocal ((pullback.fst f g).stalkMap q).hom) := sorry

end AlgebraicGeometry.Scheme
