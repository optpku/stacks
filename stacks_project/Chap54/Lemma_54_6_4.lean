/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily.PointBlowupSequence

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/- Lemma 54.6.4: under punctured-stalk base change, a morphism factors as a finite sequence
of blowups at closed points over the marked family exactly when every corresponding local
morphism factors as a finite sequence of blowups at closed points over its distinguished
closed point. Sequence realization is up to isomorphism over the base, including the
zero-length case. -/
@[stacks 0BFY]
#check (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange.existsPointBlowupSequence_iff :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).obj X ≅ Y),
    X.obj.hom.IsPointBlowupSequenceOver (Set.range s) ↔
      ∀ i, (Y i).obj.hom.IsPointBlowupSequenceOver
        ({IsLocalRing.closedPoint (S.presheaf.stalk (s i))} : Set _))

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
