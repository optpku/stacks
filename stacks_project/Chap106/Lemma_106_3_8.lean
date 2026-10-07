module

public import stacks_project.Chap106.Lemma_106_3_8_Diagonal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.IsThickening
open AlgebraicGeometry.AlgebraicStack.IsThickening.Hom
open scoped Bicategory

universe u

/- Lemma 106.3.8 (1): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously representable by schemes. -/
@[stacks 0BPV] #check diagonal_relativelyRepresentable_iff

/- Lemma 106.3.8 (2): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously affine. -/
@[stacks 0BPV] #check diagonal_affine_iff

/- Lemma 106.3.8 (3): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously surjective. -/
@[stacks 0BPV] #check diagonal_surjective_iff

/- Lemma 106.3.8 (4): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously quasi-compact. -/
@[stacks 0BPV] #check diagonal_quasiCompact_iff

/- Lemma 106.3.8 (5): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously universally closed. -/
@[stacks 0BPV] #check diagonal_universallyClosed_iff

/- Lemma 106.3.8 (6): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously integral. -/
@[stacks 0BPV] #check diagonal_isIntegralHom_iff

/- Lemma 106.3.8 (7): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously quasi-separated. -/
@[stacks 0BPV] #check diagonal_quasiSeparated_iff

/- Lemma 106.3.8 (8): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously separated. -/
@[stacks 0BPV] #check diagonal_separated_iff

/- Lemma 106.3.8 (9): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously universally injective. -/
@[stacks 0BPV] #check diagonal_universallyInjective_iff

/- Lemma 106.3.8 (10): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously universally open. -/
@[stacks 0BPV] #check diagonal_universallyOpen_iff

/- Lemma 106.3.8 (11): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously locally quasi-finite. -/
@[stacks 0BPV] #check diagonal_locallyQuasiFinite_iff

/- Lemma 106.3.8 (12): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously finite. -/
@[stacks 0BPV] #check diagonal_isFinite_iff

/- Lemma 106.3.8 (13): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously unramified. -/
@[stacks 0BPV] #check diagonal_unramified_iff

/- Lemma 106.3.8 (14): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously monomorphisms. -/
@[stacks 0BPV] #check diagonal_mono_iff

/- Lemma 106.3.8 (15): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously immersions. -/
@[stacks 0BPV] #check diagonal_isImmersion_iff

/- Lemma 106.3.8 (16): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously closed immersions. -/
@[stacks 0BPV] #check diagonal_isClosedImmersion_iff

/- Lemma 106.3.8 (17): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously proper. -/
@[stacks 0BPV] #check diagonal_proper_iff
