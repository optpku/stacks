/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Completion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.11.1 -/
@[stacks 0BG5] #check (AlgebraicGeometry.Scheme.completionStalkMap_bijective_of_baseChange :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A]
    (hfg : (maximalIdeal A).FG) (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
    let Ahat := AdicCompletion (maximalIdeal A) A
    let g : Spec (.of Ahat) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
    ∀ q : (pullback f g : Scheme),
      f (pullback.fst f g q) = closedPoint A →
        Function.Bijective
          (AdicCompletion.mapLocal ((pullback.fst f g).stalkMap q).hom))

end AlgebraicGeometry.Scheme
