/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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

/-- Integer grading identity comparing the Gysin composition degree `c + (-t)` with the
flat-pullback degree `-r`. -/
theorem gysin_flat_degree (t c r : ℕ) (hdim : (t : ℤ) - c = r) :
    (c : ℤ) + (-(t : ℤ)) = -(r : ℤ) := sorry

/-- An arrow of `Over S` agrees with the virtual-normal packaging of its underlying scheme
morphism. -/
theorem overHom_eq_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    overHom X.hom Y.hom f.left (Over.w f) = f := sorry

/-- Lemma 42.59.5: in Situation 42.7.1, if `f : X ⟶ Y` is a local complete intersection
morphism of schemes locally of finite type over `S`, the Gysin map exists for `f`, and `f` is
flat, then the Gysin class of `f` equals the flat-pullback bivariant class of Lemma 42.33.2. -/
@[stacks 0FF4]
theorem gysin_eq_flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [Flat f.left] (r : ℕ) [Scheme.Hom.RelativeDimension f.left r]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (g : P ⟶ Y) (hi : IsImmersion i.left)
    [IsClosedImmersion i.left] [IsRegularImmersion i.left]
    [hg : Smooth g.left] (hfac : i ≫ g = f)
    (t : ℕ) [Scheme.Hom.RelativeDimension g.left t]
    (c : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i.left)]
    (hdim : (t : ℤ) - c = r)
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (D : ClosedSpecialization δ X.hom P.hom i.left (Over.w i)
      (ofNormalSheaf i.left c e)) :
    Nonnegative.castGrading δ (gysin_flat_degree t c r hdim)
      (bivariantGysinClassOfFactorization δ X Y f P i g hi hg hfac
        (overHom_eq_over i ▸
          globalClassOfRank δ X.hom P.hom i.left (Over.w i)
            (ofNormalSheaf i.left c e) D c)
        (flatPullback δ g t)) =
      flatPullback δ f r := sorry

end AlgebraicGeometry.BivariantClass
