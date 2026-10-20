module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Excess
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition

/-!
# Excess base change for local complete intersection Gysin classes

The dual of the excess conormal kernel supplies the Chern factor in the
base-change formula, degree by degree on each of its clopen rank loci.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle
open Scheme.Hom.NaiveCotangent.BaseChange Gysin

/-- An immersion–smooth factorization, and hence existence of a Gysin map, is preserved
by a cartesian base change of schemes over a base. -/
theorem hasGysinMap_of_isPullback
    {S : Scheme.{u}} {X Y X' Y' : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (hf : HasGysinMap f) : HasGysinMap f' := sorry

/-- For a cartesian square of local complete intersection morphisms over a universally
catenary dimension-function base, the excess conormal kernel and its dual are finite locally free and
Gysin existence descends to the base change. There are regular-immersion–smooth
factorizations with geometric normal-bundle deformation realizations whose Gysin
coefficients satisfy the excess formula on every excess-dual rank locus, in every
integer degree. -/
theorem restrict_gysin_eq_topChern_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} [LocallyOfFiniteType g.left]
    (square : IsPullback g'.left f'.left f.left g.left)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection f'.left]
    (hf : HasGysinMap f) :
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
          exact degree ▸ c) := sorry

end AlgebraicGeometry.BivariantClass
