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

/-- Lemma 42.60.1 (1): in Situation 42.7.1, if `f : X ⟶ Y` is a smooth morphism of schemes
locally of finite type over `S`, then `Δ! ∘ pr_1! = 1` in `A^0(X)`, where `Δ` is
`pullback.diagonal f`, `pr_1` is `pullback.fst f f`, `Δ!` is `gysinSection` of `Δ`,
`pr_1!` is `flatPullback` of `pr_1` by Lemma 42.59.5, `1` is `oneOver`, and composition
is `BivariantClass.comp`. -/
@[stacks 0FBS]
theorem gysin_diagonal_comp_fst_eq_one
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Smooth f.left] (d : ℕ) [Scheme.Hom.RelativeDimension f.left d]
    [LocallyOfFiniteType (pullback f f).hom]
    [Smooth (pullback.fst f f).left]
    [Scheme.Hom.RelativeDimension (pullback.fst f f).left d]
    [IsImmersion (pullback.diagonal f).left]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank d
      (Scheme.Hom.conormalSheaf (pullback.diagonal f).left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf (pullback.diagonal f).left) ≅
      Scheme.Hom.conormalSheaf (pullback.diagonal f).left)
    (D : ClosedSpecialization δ X.hom
      ((pullback.diagonal f).left.coborderRange.ι ≫ (pullback f f).hom)
      (pullback.diagonal f).left.liftCoborder
      (factorization_over X.hom (pullback f f).hom (pullback.diagonal f).left
        (Over.w (pullback.diagonal f))
        (pullback.diagonal f).left.liftCoborder
        (pullback.diagonal f).left.coborderRange.ι
        (pullback.diagonal f).left.liftCoborder_ι)
      (ofNormalSheaf (pullback.diagonal f).left d e).toCoborder) :
    Nonnegative.castGrading δ (add_neg_cancel (d : ℤ))
        (pullback.diagonal_fst f ▸
          comp δ (pullback.diagonal f) (pullback.fst f f)
            (gysinSection δ (pullback.diagonal f) d e D)
            (flatPullback δ (pullback.fst f f) d)) =
      oneOver δ X := sorry

/-- Lemma 42.60.1 (2): in Situation 42.7.1, if `f : X ⟶ Y` is a smooth morphism of schemes
locally of finite type over `S`, then `Δ! ∘ pr_2! = 1` in `A^0(X)`, where `Δ` is
`pullback.diagonal f`, `pr_2` is `pullback.snd f f`, `Δ!` is `gysinSection` of `Δ`,
`pr_2!` is `flatPullback` of `pr_2` by Lemma 42.59.5, `1` is `oneOver`, and composition
is `BivariantClass.comp`. -/
@[stacks 0FBS]
theorem gysin_diagonal_comp_snd_eq_one
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Smooth f.left] (d : ℕ) [Scheme.Hom.RelativeDimension f.left d]
    [LocallyOfFiniteType (pullback f f).hom]
    [Smooth (pullback.snd f f).left]
    [Scheme.Hom.RelativeDimension (pullback.snd f f).left d]
    [IsImmersion (pullback.diagonal f).left]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank d
      (Scheme.Hom.conormalSheaf (pullback.diagonal f).left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf (pullback.diagonal f).left) ≅
      Scheme.Hom.conormalSheaf (pullback.diagonal f).left)
    (D : ClosedSpecialization δ X.hom
      ((pullback.diagonal f).left.coborderRange.ι ≫ (pullback f f).hom)
      (pullback.diagonal f).left.liftCoborder
      (factorization_over X.hom (pullback f f).hom (pullback.diagonal f).left
        (Over.w (pullback.diagonal f))
        (pullback.diagonal f).left.liftCoborder
        (pullback.diagonal f).left.coborderRange.ι
        (pullback.diagonal f).left.liftCoborder_ι)
      (ofNormalSheaf (pullback.diagonal f).left d e).toCoborder) :
    Nonnegative.castGrading δ (add_neg_cancel (d : ℤ))
        (pullback.diagonal_snd f ▸
          comp δ (pullback.diagonal f) (pullback.snd f f)
            (gysinSection δ (pullback.diagonal f) d e D)
            (flatPullback δ (pullback.snd f f) d)) =
      oneOver δ X := sorry

end AlgebraicGeometry.BivariantClass
