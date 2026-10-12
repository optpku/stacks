/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import stacks_project.Chap56.Lemma_56_5_2
public import stacks_project.Chap56.Lemma_56_5_5

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))

/-- Inverse of `admissibleFourierMukai`, using `fourierMukai_isEquivalence`. -/
noncomputable def admissibleFourierMukaiInv [IsAffine X] :
    RightExactCoproductLinearFunctor x y ⥤ Scheme.QCoh (Limits.pullback x y) :=
  @Functor.inv _ _ _ _ (admissibleFourierMukai x y) (fourierMukai_isEquivalence x y)

/-- Lemma 56.5.6 (1): if `X` is affine and `F : Scheme.QCoh X ⥤ Scheme.QCoh Y` is
an admissible exact functor, then the corresponding kernel on
`Limits.pullback x y` recovered by the inverse of `admissibleFourierMukai` is
flat over `X` relative to `Limits.pullback.fst x y`. -/
@[stacks 0FZG]
theorem fourierMukaiInv_flatOver_of_exact [IsAffine X]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [Admissible x y F]
    (hF : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F) :
    Scheme.Modules.flatOver
      ((inclusion _).obj
        ((admissibleFourierMukaiInv x y).obj ⟨F, inferInstance⟩))
      (Limits.pullback.fst x y) :=
  sorry

/-- Lemma 56.5.6 (2): if `X` is quasi-compact with affine diagonal and
`F : Scheme.QCoh X ⥤ Scheme.QCoh Y` is an admissible exact functor, then the
corresponding kernel `fourierMukaiKernel x y F` is flat over `X` relative to
`Limits.pullback.fst x y`. -/
@[stacks 0FZG]
theorem fourierMukaiKernel_flatOver_of_exact
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [Admissible x y F]
    (hF : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F) :
    Scheme.Modules.flatOver
      ((inclusion _).obj (fourierMukaiKernel x y
        (Classical.choose (exists_fourierMukaiReconstruction x y F)).data))
      (Limits.pullback.fst x y) :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
