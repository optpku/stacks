/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Lemma_77_11_2_InDimensions
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory

universe u

variable {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
variable (f : X ⟶ Y) (ℱ : X.Modules) (n : ℕ)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
variable (g : Y' ⟶ Y)

/- Lemma 77.11.2 (1): there is a commutative square of schemes with surjective
étale vertical arrows such that φ*ℱ is flat over V in dimensions ≥ n. -/
@[stacks 0CWS] #check
  (flatOverInDimensionsGE_iff_existsEtaleSquare ℱ f n :
    flatOverInDimensionsGE ℱ f n ↔
      ∃ sq : EtaleSquare f,
        Surjective sq.left.hom ∧ Surjective sq.right.hom ∧
          Scheme.Modules.flatOverInDimensionsGE
            ((restrictToScheme sq.left).obj ℱ) sq.map.left n)

/- Lemma 77.11.2 (2): for every commutative square of schemes with étale vertical
arrows, φ*ℱ is flat over V in dimensions ≥ n. -/
@[stacks 0CWS] #check
  (flatOverInDimensionsGE_iff_forallEtaleSquare ℱ f n :
    flatOverInDimensionsGE ℱ f n ↔
      ∀ sq : EtaleSquare f,
        Scheme.Modules.flatOverInDimensionsGE
          ((restrictToScheme sq.left).obj ℱ) sq.map.left n)

/- Lemma 77.11.2 (3): the equivalent conditions remain true after any base change
Y' ⟶ Y. -/
@[stacks 0CWS] #check
  (flatOverInDimensionsGE_pullback ℱ f n g :
    flatOverInDimensionsGE ℱ f n →
      flatOverInDimensionsGE ((pullback (Limits.pullback.fst f g)).obj ℱ)
        (Limits.pullback.snd f g) n)
