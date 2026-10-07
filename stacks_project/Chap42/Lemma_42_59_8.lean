module

public import stacks_project.Chap42.Definition_42_59_4
public import stacks_project.Chap42.Lemma_42_54_5
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.Strata
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle

/-- The integer `n` is a generic-dimension index of `x` for `f` relative to `δ` when every
generic point of an irreducible component through `x` has relative dimension `n`, as in
clause (3) of `Scheme.Hom.genericDimensionStrata_tfae`. -/
def IsGenericDimensionIndex {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) (n : ℤ) : Prop :=
  ∀ ξ : genericPoints X, x ∈ (genericPoints.component ξ : Set X) →
    f.relativeDimensionFunction δ ξ.1 = n

/-- Unfolding of `IsGenericDimensionIndex`. -/
theorem isGenericDimensionIndex_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) (n : ℤ) :
    IsGenericDimensionIndex f δ x n ↔
      ∀ ξ : genericPoints X, x ∈ (genericPoints.component ξ : Set X) →
        f.relativeDimensionFunction δ ξ.1 = n :=
  sorry

/-- A generic-dimension index of a point, when it exists, is unique. -/
theorem isGenericDimensionIndex_unique {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) {n m : ℤ}
    (hn : IsGenericDimensionIndex f δ x n)
    (hm : IsGenericDimensionIndex f δ x m) : n = m :=
  sorry

/-- An arrow of `Over S` agrees with the virtual-normal packaging of its underlying scheme
morphism. -/
theorem overHom_eq_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    overHom X.hom Y.hom f.left (Over.w f) = f := sorry

/-- Lemma 42.59.8: in Situation 42.7.1, consider a cartesian square of schemes locally of finite
type over `S`. If `f` is a local complete intersection morphism for which a Gysin map exists,
`X`, `X'`, `Y`, and `Y'` satisfy Lemma 42.42.1, the generic-dimension indices of the images of
each point of `X'` obey `n_{x'} - n_{y'} = n_x - n_y`, and
`Y'.left.presheaf.stalk (f'.left ξ)` is Cohen–Macaulay at every generic point `ξ` of `X'`, then
the Gysin class of `f` caps the fundamental class of `Y'` from Remark 42.42.2 onto the
fundamental class of `X'`, i.e. `f^![Y'] = [X']`. -/
@[stacks 0FF7]
theorem gysin_cap_fundamentalClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left)
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (c : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left c e))
    (hX : ∀ x : X.left, ∃ n, IsGenericDimensionIndex X.hom δ x n)
    (hX' : ∀ x' : X'.left, ∃ n, IsGenericDimensionIndex X'.hom δ x' n)
    (hY : ∀ y : Y.left, ∃ n, IsGenericDimensionIndex Y.hom δ y n)
    (hY' : ∀ y' : Y'.left, ∃ n, IsGenericDimensionIndex Y'.hom δ y' n)
    (hdim : ∀ (x' : X'.left) (nX' nY' nX nY : ℤ),
      IsGenericDimensionIndex X'.hom δ x' nX' →
      IsGenericDimensionIndex Y'.hom δ (f'.left x') nY' →
      IsGenericDimensionIndex X.hom δ (i.left x') nX →
      IsGenericDimensionIndex Y.hom δ (g.left (f'.left x')) nY →
      nX' - nY' = nX - nY ∧ nX - nY = -((c : ℤ) + (-(t : ℤ))))
    (hCM : ∀ ξ : genericPoints X'.left,
      CohenMacaulayRing (Y'.left.presheaf.stalk (f'.left ξ.1)))
    (n : ℤ) :
    (bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
        (overHom_eq_over ι ▸
          globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
            (ofNormalSheaf ι.left c e) D c)
        (flatPullback δ σ t)).cap i f' g square n
      (fundamentalClass_mk δ Y'.hom n) =
      fundamentalClass_mk δ X'.hom (n - ((c : ℤ) + (-(t : ℤ)))) :=
  sorry

end AlgebraicGeometry.BivariantClass
