/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap76.Lemma_76_9_7
public import stacks_project.Chap91.«91_10_5_1_TrivSqZeroExt»
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import stacks_project.Chap91.Lemma_91_14_2_LiftAlgebra
public import stacks_project.Chap91.Lemma_91_14_2_SolutionBridge
public import stacks_project.Chap91.Lemma_91_14_2_Ext1Geometric

/-!
# Translation of a flat first-order algebraic-space lift by an Ext¹ class

A class in the source geometric Ext¹ is transported by the explicit polynomial
comparison, represented by a locally surjective 91.13.2 presentation, and acts
by the genuine 91.13.3 fiber-product/pushout construction. The result is realized
using the full 76.9.7 square-zero-algebra witness. Differences use the two actual
extension evaluations on their common presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open CategoryTheory.ConcreteCategory
open Algebra Algebra.Extension Algebra.Generators MvPolynomial
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open AlgebraicGeometry.AlgebraicSpace.Thickening
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt
open TrivSqZeroExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening
namespace FlatLift

variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- Incoming differentials into degree `-1` of `NL[f]` vanish after composing with a
map out of the presentation conormal. -/
theorem naiveCotangent_d_comp_conormalHom
    (δ : cotangentSheaf f ⟶ pulledConormal t f)
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i (-1)) :
    (NL[f]).d i (-1) ≫ δ = 0 := sorry

/-- The derived `Ext¹` class of a map out of the canonical presentation conormal of
`f^♯`. The canonical self-presentation is locally surjective, so this is the
91.13.2 representative against `Q NL[f]`. -/
public def conormalHomClass (δ : cotangentSheaf f ⟶ pulledConormal t f) :
    extOneNL t f :=
  DerivedCategory.Q.map
      (HomologicalComplex.mkHomToSingle δ (naiveCotangent_d_comp_conormalHom δ)) ≫
    ((DerivedCategory.singleFunctors (Modules X)).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app (pulledConormal t f)

/-- `conormalHomClass` is `Q.map` of `mkHomToSingle`, compared with the shift of
`f^* 𝒞` from degree `-1` to degree `0`. -/
theorem conormalHomClass_def (δ : cotangentSheaf f ⟶ pulledConormal t f) :
    conormalHomClass δ =
      DerivedCategory.Q.map
          (HomologicalComplex.mkHomToSingle δ (naiveCotangent_d_comp_conormalHom δ)) ≫
        ((DerivedCategory.singleFunctors (Modules X)).shiftIso (1 : ℤ) (-1) 0
          (add_neg_cancel (1 : ℤ))).inv.app (pulledConormal t f) := sorry

/-- Unshift an Ext¹ class to a derived Hom into the degree `-1` single of
`f^* 𝒞_{Y/Y'}`. -/
def unshiftExtOne (ξ : extOneNL t f) :
    (DerivedCategory.Q).obj NL[f] ⟶
      (DerivedCategory.singleFunctor (Modules X) (-1)).obj (pulledConormal t f) :=
  ξ ≫ ((DerivedCategory.singleFunctors (Modules X)).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).hom.app (pulledConormal t f)

/-- `unshiftExtOne` is postcomposition with the single-shift identification. -/
theorem unshiftExtOne_def (ξ : extOneNL t f) :
    unshiftExtOne ξ =
      ξ ≫ ((DerivedCategory.singleFunctors (Modules X)).shiftIso (1 : ℤ) (-1) 0
          (add_neg_cancel (1 : ℤ))).hom.app (pulledConormal t f) :=
  rfl

/-- The actual solution translated by the presentation representing the geometric class. -/
def translatedSolution (ξ : extOneNL t f) (L : FlatLift t f) : LiftSolution L :=
  FirstOrderThickening.Solution.translatePresented.{u + 1, u, u}
    (toRingedExtOne t f ξ) (geometricExtOnePresentation t f ξ) (toSolution L L)

/-- Translation uses a full presentation of ξ and the genuine extension algebra of L. -/
public def translate (ξ : extOneNL t f) (L : FlatLift t f) : FlatLift t f :=
  fromSolution L (translatedSolution ξ L)

/-- The translated lift realizes precisely the solution produced by the pushout construction. -/
theorem translate_spec (ξ : extOneNL t f) (L : FlatLift t f) :
    IsRealization (f ≫ t) (translatedSolution ξ L).middle (translatedSolution ξ L).proj
      (translatedSolution ξ L).proj_squareZero (translatedSolution ξ L).structureMap
      (solution_over L (translatedSolution ξ L)) (translate ξ L).i (translate ξ L).f'
      (realizationData L (translatedSolution ξ L)).comparison :=
  (realizationData L (translatedSolution ξ L)).realizes

/-- A concrete conormal map still acts through its honest Ext¹ class; no claim is made
that every Ext¹ class comes from this one fixed presentation. -/
def translateOfLift (δ : cotangentSheaf f ⟶ pulledConormal t f) (L : FlatLift t f) : FlatLift t f :=
  translate (conormalHomClass δ) L

theorem translateOfLift_spec (δ : cotangentSheaf f ⟶ pulledConormal t f) (L : FlatLift t f) :
    translateOfLift δ L = translate (conormalHomClass δ) L := rfl

instance instFlat_translateF' (ξ : extOneNL t f) (L : FlatLift t f) :
    Flat (translate ξ L).f' := (translate ξ L).flat

instance instIsFirstOrderThickening_translateI (ξ : extOneNL t f) (L : FlatLift t f) :
    IsFirstOrderThickening (translate ξ L).i := instIsFirstOrderThickening_i (translate ξ L)

theorem translate_isPullback (ξ : extOneNL t f) (L : FlatLift t f) :
    IsPullback f (translate ξ L).i t (translate ξ L).f' := (translate ξ L).isPullback

/-- Difference uses the two actual extension algebras, their common presentation,
and the inverse of the same geometric polynomial comparison. -/
public def liftObstruction (L₁ L₂ : FlatLift t f) : extOneNL t f :=
  fromRingedExtOne t f
    (FirstOrderThickening.Solution.differencePresented.{u + 1, u, u}
      (toSolution L₁ L₁) (toSolution L₁ L₂))

theorem liftObstruction_spec (L₁ L₂ : FlatLift t f) :
    liftObstruction L₁ L₂ = fromRingedExtOne t f
      (FirstOrderThickening.Solution.Difference.extClass.{u + 1, u, u} (toSolution L₁ L₁) (toSolution L₁ L₂)) := rfl

/-- The genuine extension difference translates the first geometric lift to the second. -/
theorem exists_algebraDiff (L₁ L₂ : FlatLift t f) :
    Nonempty (Hom (translate (liftObstruction L₁ L₂) L₁) L₂) := sorry

theorem liftObstruction_translate (ξ : extOneNL t f) (L : FlatLift t f) :
    liftObstruction L (translate ξ L) = ξ := sorry

theorem liftObstruction_eq_zero_iff (L₁ L₂ : FlatLift t f) :
    liftObstruction L₁ L₂ = 0 ↔ Nonempty (Hom L₁ L₂) := sorry

end FlatLift
end AlgebraicGeometry.AlgebraicSpace.Thickening
