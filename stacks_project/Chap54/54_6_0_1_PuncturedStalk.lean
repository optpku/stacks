/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily

/-! This source-facing module retains typed compatibility checks for the shared family API. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen

/- The family base-change functor has the complete source-facing type. -/
#check (puncturedStalkBaseChange :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι],
    FinitePresentationIsoOverOpen U ⥤
      ((i : ι) → FinitePresentationIsoOverOpen
        (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i)))))

#check (puncturedStalkBaseChange_comp_eval :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (i : ι),
    puncturedStalkBaseChange S s hs_closed hs_pairwise U hU ⋙
        CategoryTheory.Pi.eval
          (fun j ↦ FinitePresentationIsoOverOpen
            (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s j)))) i =
      baseChangeRestrict (S.fromSpecStalk (s i)) U
        (stalkOpenIntersection_eq_puncturedOpen_of_compl_range
          S s hs_closed hs_pairwise U hU i).ge)

#check (puncturedStalkBaseChange_obj_hom :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U) (i : ι),
    ((puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).obj X i).obj.hom =
      pullback.snd X.obj.hom (S.fromSpecStalk (s i)))

#check (puncturedStalkBaseChange_map_hom :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    {X Y : FinitePresentationIsoOverOpen U} (f : X ⟶ Y) (i : ι),
    ((puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).map f i).hom =
      (Over.pullback (S.fromSpecStalk (s i))).map f.hom)

end AlgebraicGeometry.FinitePresentationIsoOverOpen
