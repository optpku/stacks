/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-presentation gluing over a finite family of stalks

This module packages the product categories, restriction functors, and categorical pullback used
to compare finite-presentation schemes with gluing data over finitely many local schemes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The product of the finite-presentation categories over the intersections of a family of stalk
schemes with an open subscheme. -/
abbrev finitePresentationStalkOpenProduct
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) : Type (u + 1) :=
  (i : ι) → FinitePresentationOver (stalkOpenIntersection S U (s i)).toScheme

/-- The product of the finite-presentation categories over a family of local schemes. -/
abbrev finitePresentationStalkProduct
    {ι : Type u} (S : Scheme.{u}) (s : ι → S) : Type (u + 1) :=
  (i : ι) → FinitePresentationOver (Spec (S.presheaf.stalk (s i)))

/-- The restriction functor from finite-presentation schemes over an open subscheme to their
pullbacks over a family of stalk-open intersections. -/
abbrev finitePresentationToStalkOpenProduct
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) :
    FinitePresentationOver U.toScheme ⥤ finitePresentationStalkOpenProduct S U s where
  obj X := fun i ↦ FinitePresentationOver.baseChange ((S.fromSpecStalk (s i)) ∣_ U) |>.obj X
  map f := fun i ↦ FinitePresentationOver.baseChange ((S.fromSpecStalk (s i)) ∣_ U) |>.map f

/-- The restriction functor from finite-presentation schemes over a family of local schemes to
their pullbacks over the associated stalk-open intersections. -/
abbrev finitePresentationStalkProductToStalkOpenProduct
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) :
    finitePresentationStalkProduct S s ⥤ finitePresentationStalkOpenProduct S U s where
  obj X := fun i ↦ FinitePresentationOver.baseChange
    (stalkOpenIntersection S U (s i)).ι |>.obj (X i)
  map f := fun i ↦ FinitePresentationOver.baseChange
    (stalkOpenIntersection S U (s i)).ι |>.map (f i)

/-- The categorical pullback of finite-presentation schemes over an open subscheme and over a
family of local schemes, compared over the corresponding stalk-open intersections. -/
abbrev finitePresentationStalkFamilyGluingCategory
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) : Type (u + 1) :=
  CategoricalPullback
    (finitePresentationToStalkOpenProduct S U s)
    (finitePresentationStalkProductToStalkOpenProduct S U s)

/-- If an open subscheme is the complement of the range of an injective finite family of closed
points, then its pullback to each local scheme is the punctured spectrum of the local ring. -/
theorem stalkOpenIntersection_eq_puncturedOpen_of_compl_range
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) (i : ι) :
    stalkOpenIntersection S U (s i) =
      PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i)) := sorry

/-- The canonical identification, for each point of the family, of the two restrictions to
the stalk-open intersection. -/
noncomputable def finitePresentationStalkFamilyGluingIso
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) :
    FinitePresentationOver.baseChange U.ι ⋙ finitePresentationToStalkOpenProduct S U s ≅
      Functor.pi' (fun i ↦ FinitePresentationOver.baseChange (S.fromSpecStalk (s i))) ⋙
        finitePresentationStalkProductToStalkOpenProduct S U s :=
  NatIso.pi' fun i ↦ finitePresentationStalkGluingIso S U (s i)

/-- The restriction functor of Stacks 0E8Q: `X → S` goes to its restriction over `U`, its
restrictions over the local schemes `Spec(𝒪_{S,s_i})`, and the canonical identifications over
the punctured local schemes. -/
noncomputable def finitePresentationStalkFamilyGluingFunctor
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) :
    FinitePresentationOver S ⥤ finitePresentationStalkFamilyGluingCategory S U s :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    { fst := FinitePresentationOver.baseChange U.ι
      snd := Functor.pi' (fun i ↦ FinitePresentationOver.baseChange (S.fromSpecStalk (s i)))
      iso := finitePresentationStalkFamilyGluingIso S U s }

/-- The `U`-component of the family gluing restriction functor is base change to `U`. -/
@[simp]
theorem finitePresentationStalkFamilyGluingFunctor_obj_fst
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) (X : FinitePresentationOver S) :
    ((finitePresentationStalkFamilyGluingFunctor S U s).obj X).fst =
      (FinitePresentationOver.baseChange U.ι).obj X :=
  rfl

/-- The `i`-th local component of the family gluing restriction functor is base change to
`Spec(𝒪_{S,s_i})`. -/
@[simp]
theorem finitePresentationStalkFamilyGluingFunctor_obj_snd
    {ι : Type u} (S : Scheme.{u}) (U : S.Opens) (s : ι → S) (X : FinitePresentationOver S)
    (i : ι) :
    ((finitePresentationStalkFamilyGluingFunctor S U s).obj X).snd i =
      (FinitePresentationOver.baseChange (S.fromSpecStalk (s i))).obj X :=
  rfl

/-- Stacks 0E8Q: for a nonempty finite family of distinct closed points with quasi-compact
complement `U`, the restriction functor to family gluing data is an equivalence. -/
@[stacks 0E8Q]
theorem finitePresentationStalkFamilyGluingFunctor_isEquivalence
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ)
    [QuasiCompact U.ι] :
    (finitePresentationStalkFamilyGluingFunctor S U s).IsEquivalence := sorry

end AlgebraicGeometry
