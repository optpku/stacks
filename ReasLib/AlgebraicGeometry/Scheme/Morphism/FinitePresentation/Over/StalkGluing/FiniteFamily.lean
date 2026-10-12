/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing

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

/-- Finite-presentation schemes over a scheme are equivalent to compatible finite-presentation
schemes over the complement of a nonempty finite family of distinct closed points and over the
corresponding local schemes. -/
theorem finitePresentationOver_equivalence_stalkFamilyGluing
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ)
    [QuasiCompact U.ι] :
    Nonempty
      (FinitePresentationOver S ≌ finitePresentationStalkFamilyGluingCategory S U s) := sorry

end AlgebraicGeometry
