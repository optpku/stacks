module

public import stacks_project.Chap42.Definition_42_59_4
public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle

/-- An arrow of `Over S` agrees with the virtual-normal packaging of its underlying scheme
morphism. -/
theorem overHom_eq_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    overHom X.hom Y.hom f.left (Over.w f) = f := sorry

/-- Lemma 42.59.3: in Situation 42.7.1, if `f : X ⟶ Y` is a local complete intersection
morphism of schemes locally of finite type over `S`, the bivariant class `f^!` is independent
of the choice of factorization `f = g ∘ i` with `g` smooth, provided one exists. Here `f^!`
means `bivariantGysinClassOfFactorization` of the rank-`r` closed Gysin class of `i` and
`flatPullback` of the smooth factor. -/
@[stacks 0FF2]
theorem gysin_eq_of_factorization
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (g : P ⟶ Y) (hi : IsImmersion i.left)
    [IsClosedImmersion i.left] [IsRegularImmersion i.left]
    [hg : Smooth g.left] (hfac : i ≫ g = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension g.left t]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (D : ClosedSpecialization δ X.hom P.hom i.left (Over.w i)
      (ofNormalSheaf i.left r e))
    {P' : Over S} [LocallyOfFiniteType P'.hom]
    (i' : X ⟶ P') (g' : P' ⟶ Y) (hi' : IsImmersion i'.left)
    [IsClosedImmersion i'.left] [IsRegularImmersion i'.left]
    [hg' : Smooth g'.left] (hfac' : i' ≫ g' = f)
    (t' : ℕ) [Scheme.Hom.RelativeDimension g'.left t']
    (r' : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r' (Scheme.Hom.conormalSheaf i'.left)]
    (e' : Scheme.Modules.dual (Scheme.Hom.normalSheaf i'.left) ≅
      Scheme.Hom.conormalSheaf i'.left)
    (D' : ClosedSpecialization δ X.hom P'.hom i'.left (Over.w i')
      (ofNormalSheaf i'.left r' e'))
    (hdeg : (r : ℤ) + (-(t : ℤ)) = (r' : ℤ) + (-(t' : ℤ))) :
    Nonnegative.castGrading δ hdeg
      (bivariantGysinClassOfFactorization δ X Y f P i g hi hg hfac
        (overHom_eq_over i ▸
          globalClassOfRank δ X.hom P.hom i.left (Over.w i)
            (ofNormalSheaf i.left r e) D r)
        (flatPullback δ g t)) =
      bivariantGysinClassOfFactorization δ X Y f P' i' g' hi' hg' hfac'
        (overHom_eq_over i' ▸
          globalClassOfRank δ X.hom P'.hom i'.left (Over.w i')
            (ofNormalSheaf i'.left r' e') D' r')
        (flatPullback δ g' t') := sorry

end AlgebraicGeometry.BivariantClass
