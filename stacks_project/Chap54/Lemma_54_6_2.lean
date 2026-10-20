/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily.Properties

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/- Lemma 54.6.2 (1): under base change at a finite nonempty family of distinct closed
points, a morphism is separated if and only if every corresponding punctured-stalk
morphism is separated. -/
@[stacks 0BFW] #check
  (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange.isSeparated_iff :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (FinitePresentationIsoOverOpen.puncturedStalkBaseChange
      S s hs_closed hs_pairwise U hU).obj X ≅ Y),
    IsSeparated X.obj.hom ↔ ∀ i, IsSeparated (Y i).obj.hom)

/- Lemma 54.6.2 (2): under base change at a finite nonempty family of distinct closed
points, a morphism is proper if and only if every corresponding punctured-stalk
morphism is proper. -/
@[stacks 0BFW] #check
  (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange.isProper_iff :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (FinitePresentationIsoOverOpen.puncturedStalkBaseChange
      S s hs_closed hs_pairwise U hU).obj X ≅ Y),
    IsProper X.obj.hom ↔ ∀ i, IsProper (Y i).obj.hom)

/- Lemma 54.6.2 (3): under base change at a finite nonempty family of distinct closed
points, a morphism is finite if and only if every corresponding punctured-stalk
morphism is finite. -/
@[stacks 0BFW] #check
  (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange.isFinite_iff :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (FinitePresentationIsoOverOpen.puncturedStalkBaseChange
      S s hs_closed hs_pairwise U hU).obj X ≅ Y),
    IsFinite X.obj.hom ↔ ∀ i, IsFinite (Y i).obj.hom)

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
