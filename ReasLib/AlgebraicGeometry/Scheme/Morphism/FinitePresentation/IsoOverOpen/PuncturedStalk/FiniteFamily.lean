module

public import Mathlib.CategoryTheory.Pi.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing.FiniteFamily

/-!
# Base change at a finite family of punctured stalks

This module assembles the base-change functors at a finite family of closed points into a
single functor valued in their dependent product category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen

/-- Base change at every point of a finite family, restricted to the corresponding punctured
local schemes. -/
noncomputable def puncturedStalkBaseChange
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι] :
    FinitePresentationIsoOverOpen U ⥤
      ((i : ι) → FinitePresentationIsoOverOpen
        (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i)))) :=
  Functor.pi' fun i ↦
    baseChangeRestrict (S.fromSpecStalk (s i)) U
      (stalkOpenIntersection_eq_puncturedOpen_of_compl_range
        S s hs_closed hs_pairwise U hU i).ge

/-- Evaluating the punctured-stalk family functor at `i` gives the corresponding restricted
base-change functor. -/
theorem puncturedStalkBaseChange_comp_eval
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (i : ι) :
    puncturedStalkBaseChange S s hs_closed hs_pairwise U hU ⋙
        CategoryTheory.Pi.eval
          (fun j ↦ FinitePresentationIsoOverOpen
            (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s j)))) i =
      baseChangeRestrict (S.fromSpecStalk (s i)) U
        (stalkOpenIntersection_eq_puncturedOpen_of_compl_range
          S s hs_closed hs_pairwise U hU i).ge := sorry

/-- The structural map in coordinate `i` is the second projection of the ordinary pullback. -/
theorem puncturedStalkBaseChange_obj_hom
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U) (i : ι) :
    ((puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).obj X i).obj.hom =
      pullback.snd X.obj.hom (S.fromSpecStalk (s i)) := sorry

/-- The map in coordinate `i`, after forgetting the open condition, is the map induced by the
ordinary slice pullback. -/
theorem puncturedStalkBaseChange_map_hom
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    {X Y : FinitePresentationIsoOverOpen U} (f : X ⟶ Y) (i : ι) :
    ((puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).map f i).hom =
      (Over.pullback (S.fromSpecStalk (s i))).map f.hom := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen
