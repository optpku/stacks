/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_59_2
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The grading identity for composing a degree-`p` class with a degree-`-d` smooth
Gysin class. -/
theorem compSmooth_degree (p : ℤ) (d : ℕ) : p + (-(d : ℤ)) = p - (d : ℤ) := sorry

/-- Composition with `g! = flatPullback δ g d` as an additive map
`A^p(X ⟶ Y) →+ A^{p - d}(X ⟶ Z)`. -/
noncomputable def compSmooth
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    BivariantClass δ f p →+ BivariantClass δ (f ≫ g) (p - (d : ℤ)) where
  toFun c := Nonnegative.castGrading δ (compSmooth_degree p d)
    (comp δ f g c (flatPullback δ g d))
  map_zero' := sorry
  map_add' := sorry

/-- Composition with the smooth Gysin class `g!` is bijective on homogeneous
bivariant groups. -/
theorem compSmooth_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    Function.Bijective (compSmooth δ f g d p) := sorry

/-- Proposition 42.60.2: in Situation 42.7.1, if `f : X ⟶ Y` and `g : Y ⟶ Z` are
morphisms of schemes locally of finite type over `S` and `g` is smooth of relative
dimension `d`, then the homogeneous bivariant groups are canonically identified by
`A^p(X ⟶ Y) = A^{p - d}(X ⟶ Z)`. The identifying additive equivalence is composition
with `g! = flatPullback δ g d ∈ A^{-d}(Y ⟶ Z)`; the source inverse is restriction of
`Δ! = gysinSection` of `pullback.diagonal g` composed with restriction of the target
class. -/
@[stacks 0FBT]
noncomputable def compSmoothEquiv
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    BivariantClass δ f p ≃+ BivariantClass δ (f ≫ g) (p - (d : ℤ)) where
  toFun := compSmooth δ f g d p
  invFun := Function.invFun (compSmooth δ f g d p)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `compSmoothEquiv` is composition with the smooth Gysin class. -/
theorem compSmoothEquiv_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ)
    (c : BivariantClass δ f p) :
    compSmoothEquiv δ f g d p c = compSmooth δ f g d p c := sorry

/-- The graph morphism `X ⟶ X ×_Z Y` of `f` over `Z`. -/
noncomputable def graphOver {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ pullback (f ≫ g) g :=
  pullback.lift (𝟙 X) f (Category.id_comp (f ≫ g))

/-- The two projections of `X ×_Z Y` agree after composing with `g` and `f ≫ g`. -/
theorem fiberComparison_comm {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullback.fst (f ≫ g) g ≫ f) ≫ g = pullback.snd (f ≫ g) g ≫ g := sorry

/-- The comparison morphism `X ×_Z Y ⟶ Y ×_Z Y` over the identity of `Y → Z`. -/
noncomputable def fiberComparison {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) g ⟶ pullback g g :=
  pullback.lift (pullback.fst (f ≫ g) g ≫ f) (pullback.snd (f ≫ g) g)
    (fiberComparison_comm f g)

/-- The graph morphism followed by `pr₂ : X ×_Z Y ⟶ Y` recovers `f`. -/
theorem graphOver_comp_snd {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    graphOver f g ≫ pullback.snd (f ≫ g) g = f := sorry

/-- The displayed square of `X ×_Z Y` against `g : Y ⟶ Z` is cartesian. -/
theorem fiberProduct_isPullback {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) g).left (pullback.snd (f ≫ g) g).left
      (f ≫ g).left g.left := sorry

/-- The graph square of `f` against the diagonal of `g` is cartesian. -/
theorem graphOver_isPullback {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback f.left (graphOver f g).left
      (pullback.diagonal g).left (fiberComparison f g).left := sorry

/-- The grading identity for composing a degree-`d` diagonal Gysin class with a
degree-`p - d` restricted class. -/
theorem compSmoothInv_degree (p : ℤ) (d : ℕ) :
    (d : ℤ) + (p - (d : ℤ)) = p := sorry

/-- The source inverse of `compSmooth`, sending `c'` to `res(Δ!) ∘ res(c')` along the
graph square of `f` and the cartesian square of `X ×_Z Y`. Here `Δ!` is
`gysinSection` of `pullback.diagonal g`. -/
noncomputable def compSmoothInv
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ)
    [LocallyOfFiniteType (pullback g g).hom]
    [LocallyOfFiniteType (pullback (f ≫ g) g).hom]
    [LocallyOfFiniteType (fiberComparison f g).left]
    [IsImmersion (pullback.diagonal g).left]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank d
      (Scheme.Hom.conormalSheaf (pullback.diagonal g).left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf (pullback.diagonal g).left) ≅
      Scheme.Hom.conormalSheaf (pullback.diagonal g).left)
    (D : ClosedSpecialization δ Y.hom
      ((pullback.diagonal g).left.coborderRange.ι ≫ (pullback g g).hom)
      (pullback.diagonal g).left.liftCoborder
      (factorization_over Y.hom (pullback g g).hom (pullback.diagonal g).left
        (Over.w (pullback.diagonal g))
        (pullback.diagonal g).left.liftCoborder
        (pullback.diagonal g).left.coborderRange.ι
        (pullback.diagonal g).left.liftCoborder_ι)
      (ofNormalSheaf (pullback.diagonal g).left d e).toCoborder)
    (c' : BivariantClass δ (f ≫ g) (p - (d : ℤ))) :
    BivariantClass δ f p :=
  graphOver_comp_snd f g ▸
    Nonnegative.castGrading δ (compSmoothInv_degree p d)
      (comp δ (graphOver f g) (pullback.snd (f ≫ g) g)
        (restrict δ f (graphOver f g) (fiberComparison f g)
          (graphOver_isPullback f g) d
          (gysinSection δ (pullback.diagonal g) d e D))
        (restrict δ (pullback.fst (f ≫ g) g) (pullback.snd (f ≫ g) g) g
          (fiberProduct_isPullback f g) (p - (d : ℤ)) c'))

/-- Given diagonal Gysin data, the abstract inverse of `compSmoothEquiv` agrees with
the source map `res(Δ!) ∘ res(c')`. -/
theorem compSmoothEquiv_symm_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ)
    [LocallyOfFiniteType (pullback g g).hom]
    [LocallyOfFiniteType (pullback (f ≫ g) g).hom]
    [LocallyOfFiniteType (fiberComparison f g).left]
    [IsImmersion (pullback.diagonal g).left]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank d
      (Scheme.Hom.conormalSheaf (pullback.diagonal g).left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf (pullback.diagonal g).left) ≅
      Scheme.Hom.conormalSheaf (pullback.diagonal g).left)
    (D : ClosedSpecialization δ Y.hom
      ((pullback.diagonal g).left.coborderRange.ι ≫ (pullback g g).hom)
      (pullback.diagonal g).left.liftCoborder
      (factorization_over Y.hom (pullback g g).hom (pullback.diagonal g).left
        (Over.w (pullback.diagonal g))
        (pullback.diagonal g).left.liftCoborder
        (pullback.diagonal g).left.coborderRange.ι
        (pullback.diagonal g).left.liftCoborder_ι)
      (ofNormalSheaf (pullback.diagonal g).left d e).toCoborder)
    (c' : BivariantClass δ (f ≫ g) (p - (d : ℤ))) :
    (compSmoothEquiv δ f g d p).symm c' = compSmoothInv δ f g d p e D c' := sorry

end AlgebraicGeometry.BivariantClass
