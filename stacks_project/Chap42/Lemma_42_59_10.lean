/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.BaseChange
public import stacks_project.Chap42.Lemma_42_59_5
public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom.NaiveCotangent.BaseChange
open Scheme.Hom Scheme.Hom.VirtualNormalBundle BivariantClass.Gysin

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The Gysin class of an immersion-smooth factorization, formed from the rank-`r` canonical
normal-bundle class and the flat pullback of relative dimension `t`. -/
noncomputable def canonicalGysinClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (h : P ⟶ Y) (hi : IsImmersion i.left)
    [IsClosedImmersion i.left] (hh : Smooth h.left) (hfac : i ≫ h = f)
    (V : Scheme.Hom.VirtualNormalBundle i.left)
    (D : ClosedSpecialization δ X.hom P.hom i.left (Over.w i) V)
    (r t : ℕ) [Scheme.Hom.RelativeDimension h.left t] :
    BivariantClass δ f ((r : ℤ) + (-(t : ℤ))) :=
  bivariantGysinClassOfFactorization δ X Y f P i h hi hh hfac
    (overHom_eq_over i ▸
      globalClassOfRank δ X.hom P.hom i.left (Over.w i) V D r)
    (flatPullback δ h t)

/-- Transport a homogeneous bivariant class along `Category.id_comp`. -/
noncomputable def idCompCast
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} (c : BivariantClass δ (𝟙 X ≫ f) p) :
    BivariantClass δ f p :=
  Category.id_comp f ▸ c

/- Lemma 42.59.10: for a cartesian square of schemes locally of finite type over the
base of Situation 42.7.1, with both vertical maps lci and a Gysin map for the unprimed
map, the actual excess conormal kernel is finite locally free and the primed Gysin
map exists. Regular-immersion–smooth factorizations and their geometric deformation
realizations exist, and the excess formula holds simultaneously on every excess-dual
rank locus r and in every integer degree p, with primed degree p - r. This includes
varying normal ranks and smooth relative dimensions; the factorization coefficients
are independent of realization by gysin_eq_of_factorization. -/
@[stacks 0FV9] #check
  (AlgebraicGeometry.BivariantClass.restrict_gysin_eq_topChern_comp :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [LocallyOfFiniteType g.left]
    (square : IsPullback g'.left f'.left f.left g.left)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'.left]
    (hf : HasGysinMap f),
    ∃ (finiteFreeC : (excessConormal square).IsFiniteLocallyFree)
      (finiteFreeDual : (excessConormalDual square).IsFiniteLocallyFree),
    HasGysinMap f' ∧
    ∃ (P : Over S) (finiteTypeP : LocallyOfFiniteType P.hom)
      (i : X ⟶ P) (h : P ⟶ Y) (regularI : IsRegularImmersion i.left)
      (smoothH : Smooth h.left) (hfac : i ≫ h = f),
    ∃ (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
      (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
        i.left.liftCoborder
        (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
        (normalBundle i.left e).toCoborder),
    ∃ (P' : Over S) (finiteTypeP' : LocallyOfFiniteType P'.hom)
      (i' : X' ⟶ P') (h' : P' ⟶ Y') (regularI' : IsRegularImmersion i'.left)
      (smoothH' : Smooth h'.left) (hfac' : i' ≫ h' = f'),
    ∃ (e' : Scheme.Modules.dual (normalSheaf i'.left) ≅ conormalSheaf i'.left)
      (D' : ClosedDeformation X'.hom (i'.left.coborderRange.ι ≫ P'.hom)
        i'.left.liftCoborder
        (by rw [← Category.assoc, i'.left.liftCoborder_ι]; exact Over.w i')
        (normalBundle i'.left e').toCoborder),
    ∀ (r : ℕ) (p : ℤ),
      let U := (Scheme.Modules.rankClopen (excessConormalDual square) r).toOpens
      let fU := ComponentRestriction.hom f' U ⊤ (by simp)
      ComponentRestriction.restrict δ f' p U ⊤ (by simp)
          (restrict δ g' f' g square p
            (factorizationClassDegree δ f i h hfac e D p)) =
        (by
          have c := comp δ (𝟙 (ComponentRestriction.over X' U)) fU
            (ChernClass.rankComponent δ X'.hom (excessConormalDual square) r
              ⟨r, Nat.lt_succ_self r⟩)
            (ComponentRestriction.restrict δ f' (p - r) U ⊤ (by simp)
              (factorizationClassDegree δ f' i' h' hfac' e' D' (p - r)))
          rw [Category.id_comp] at c
          have degree : (r : ℤ) + (p - r) = p := by omega
          exact degree ▸ c))

end AlgebraicGeometry.BivariantClass
