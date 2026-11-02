/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap54.Lemma_54_6_4
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily.NormalizedBlowupSequence

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/- Lemma 54.6.5, corrected normal-base form for absolute normalization.
The printed 0BFZ has only a finite-components assumption; that broader statement is false:
a normalized blowup changes nonnormal untouched components, even when the marked complement
is normal. The native theorem documents a surface/cusp counterexample. We retain the tag
as a source reference and expose the additional normality hypothesis in this exact signature.
Endpoints are compared up to slice isomorphism. -/
@[stacks 0BFZ] #check
  (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange.existsNormalizedBlowupSequence_iff :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens S]
    (hS_normal : S.isNormal)
    (s : ι → S) (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).obj X ≅ Y),
    X.obj.hom.IsNormalizedBlowupSequenceOver (Set.range s) ↔
      ∀ i, (Y i).obj.hom.IsNormalizedBlowupSequenceOver
        ({IsLocalRing.closedPoint (S.presheaf.stalk (s i))} : Set _))

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
