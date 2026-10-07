module

public import stacks_project.Chap42.Lemma_42_59_5
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle

/-- Lemma 42.59.7: in Situation 42.7.1, consider a cartesian square of schemes locally of
finite type over `S`. If `f : X ⟶ Y` is a local complete intersection morphism for which a
Gysin map exists, given by a closed regular immersion followed by a smooth morphism, then
every homogeneous class `c` on `h : Y'' ⟶ Y'` commutes with the restriction of the Gysin
class of `f` along that square. Here `f^!` is `bivariantGysinClassOfFactorization` of the
rank-`r` closed Gysin class and `flatPullback` of the smooth factor, `res(f^!)` is
`restrict` along the right-hand cartesian square as in Remark 42.33.5, and commute is
`Commute` as in Remark 42.33.6. -/
@[stacks 0FF6]
theorem gysin_restrict_commute
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' Y'' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType Y''.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left]
    [hσ : Smooth σ.left] (hfac : ι ≫ σ = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType f'.left]
    (square : IsPullback i.left f'.left f.left g.left)
    (h : Y'' ⟶ Y') [LocallyOfFiniteType h.left]
    (q : ℤ) (c : BivariantClass δ h q) :
    Commute δ h f' c
      (restrict δ i f' g square ((r : ℤ) + (-(t : ℤ)))
        (bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
          (overHom_eq_over ι ▸
            globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
              (ofNormalSheaf ι.left r e) D r)
          (flatPullback δ σ t))) :=
  sorry

end AlgebraicGeometry.BivariantClass
