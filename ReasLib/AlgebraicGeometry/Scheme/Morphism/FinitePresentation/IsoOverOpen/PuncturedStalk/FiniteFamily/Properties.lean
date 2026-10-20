/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/-- A morphism in the finite punctured-stalk family correspondence is separated exactly when
each corresponding local morphism is separated. -/
theorem isSeparated_iff
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (FinitePresentationIsoOverOpen.puncturedStalkBaseChange
      S s hs_closed hs_pairwise U hU).obj X ≅ Y) :
    IsSeparated X.obj.hom ↔ ∀ i, IsSeparated (Y i).obj.hom := sorry

/-- A morphism in the finite punctured-stalk family correspondence is proper exactly when each
corresponding local morphism is proper. -/
theorem isProper_iff
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (FinitePresentationIsoOverOpen.puncturedStalkBaseChange
      S s hs_closed hs_pairwise U hU).obj X ≅ Y) :
    IsProper X.obj.hom ↔ ∀ i, IsProper (Y i).obj.hom := sorry

/-- A morphism in the finite punctured-stalk family correspondence is finite exactly when each
corresponding local morphism is finite. -/
theorem isFinite_iff
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (FinitePresentationIsoOverOpen.puncturedStalkBaseChange
      S s hs_closed hs_pairwise U hU).obj X ≅ Y) :
    IsFinite X.obj.hom ↔ ∀ i, IsFinite (Y i).obj.hom := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
