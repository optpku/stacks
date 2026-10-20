/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# The flat-in-dimensions functor as a functor of points on schemes over `S`

Situation 77.11.4 defines `F_n` as a subterminal functor on schemes over `Y`.
Algebraic-space structure and morphisms are expressed on `(Over S)ᵒᵖ ⥤ Type u`,
so this module records the corresponding subfunctor of `Y.functorOfPoints`.

Relative flatness in dimensions uses the Comparison-side `flatOverAt` of
Theorem 77.4.7, which is the same étale-chart criterion as `Lemma_67_31_3_FlatOver`
but can be imported together with relative purity.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

/-- The pullback of `ℱ` to `X ×_Y T` is flat over `T` in dimensions at least `n`
when every point of failure of relative flatness has residue-field transcendence
degree less than `n`. -/
def isFlatInDimensions (T : SchemeOver Y) : Prop :=
  ∀ x : Points (Modules.baseChangeSpace f T.hom),
    ¬ Modules.flatOverAt (Modules.baseChangeModule f T.hom ℱ) (pullback.snd f T.hom) x →
      residueFieldTranscendenceDegreeAt (pullback.snd f T.hom) x < (n : ℕ∞)

/-- Relative flatness in dimensions at least `n` after base change is the
pointwise residue-field characterization of Theorem 77.4.7. -/
theorem isFlatInDimensions_iff (T : SchemeOver Y) :
    isFlatInDimensions f ℱ n T ↔
      ∀ x : Points (Modules.baseChangeSpace f T.hom),
        ¬ Modules.flatOverAt (Modules.baseChangeModule f T.hom ℱ)
            (pullback.snd f T.hom) x →
          residueFieldTranscendenceDegreeAt (pullback.snd f T.hom) x < (n : ℕ∞) :=
  sorry

/-- The flattening-in-dimensions functor of Situation 77.11.4, as a subfunctor of the
functor of points of `Y` on schemes over `S`: a morphism `ofOver T ⟶ Y` lies in `F_n`
precisely when the pullback of `ℱ` along it is flat over `T` in dimensions at least `n`. -/
def flatInDimensionsOverSSubfunctor : Subfunctor Y.functorOfPoints where
  obj T := {φ | isFlatInDimensions f ℱ n (SchemeOver.mk (yonedaEquiv.symm φ))}
  map := sorry

/-- Membership in the `(Sch/S)` flat-in-dimensions subfunctor is relative flatness in
dimensions at least `n` of the pullback of `ℱ` along the corresponding morphism
`ofOver T ⟶ Y`. -/
theorem mem_flatInDimensionsOverSSubfunctor {T : Over S}
    (φ : Y.functorOfPoints.obj (op T)) :
    φ ∈ (flatInDimensionsOverSSubfunctor f ℱ n).obj (op T) ↔
      isFlatInDimensions f ℱ n (SchemeOver.mk (yonedaEquiv.symm φ)) :=
  sorry

/-- The flattening-in-dimensions functor of Situation 77.11.4, as a functor
`(Over S)ᵒᵖ ⥤ Type u`. -/
def flatInDimensionsOverSFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (flatInDimensionsOverSSubfunctor f ℱ n).toFunctor

/-- `flatInDimensionsOverSFunctor f ℱ n` is the underlying functor of
`flatInDimensionsOverSSubfunctor f ℱ n`. -/
theorem flatInDimensionsOverSFunctor_def :
    flatInDimensionsOverSFunctor f ℱ n =
      (flatInDimensionsOverSSubfunctor f ℱ n).toFunctor :=
  sorry

/-- The structural morphism `F_n ⟶ Y` of functors of points. -/
def flatInDimensionsOverSFunctor_toY :
    flatInDimensionsOverSFunctor f ℱ n ⟶ Y.functorOfPoints :=
  (flatInDimensionsOverSSubfunctor f ℱ n).ι

/-- `flatInDimensionsOverSFunctor_toY f ℱ n` is the subfunctor inclusion of
`flatInDimensionsOverSSubfunctor f ℱ n`. -/
theorem flatInDimensionsOverSFunctor_toY_eq :
    flatInDimensionsOverSFunctor_toY f ℱ n =
      (flatInDimensionsOverSSubfunctor f ℱ n).ι :=
  sorry

/-- A scheme `T` over `S` has an `F_n`-point if and only if some morphism `ofOver T ⟶ Y`
makes the pullback of `ℱ` flat over `T` in dimensions at least `n`. -/
theorem flatInDimensionsOverSFunctor_nonempty_iff (T : Over S) :
    Nonempty ((flatInDimensionsOverSFunctor f ℱ n).obj (op T)) ↔
      ∃ a : ofOver T ⟶ Y, isFlatInDimensions f ℱ n (SchemeOver.mk a) :=
  sorry

namespace flatInDimensionsOverSFunctor

/-- The algebraic space representing the `(Sch/S)` flat-in-dimensions functor, when that
functor is an algebraic space. -/
def space [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)

/-- The functor of points of `space f ℱ n` is `flatInDimensionsOverSFunctor f ℱ n`. -/
theorem space_functorOfPoints
    [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    (space f ℱ n).functorOfPoints = flatInDimensionsOverSFunctor f ℱ n :=
  sorry

/-- The structural morphism from the flat-in-dimensions space to `Y`. -/
def toY [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    space f ℱ n ⟶ Y :=
  flatInDimensionsOverSFunctor_toY f ℱ n

/-- `toY f ℱ n` is the functor-of-points morphism `flatInDimensionsOverSFunctor_toY f ℱ n`. -/
theorem toY_eq [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    toY f ℱ n = flatInDimensionsOverSFunctor_toY f ℱ n :=
  sorry

end flatInDimensionsOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Flattening
