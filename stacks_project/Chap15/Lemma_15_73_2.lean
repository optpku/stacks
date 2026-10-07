module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Duality.ModuleCat
import StacksCheckRecall

/-!
# Dualizable complexes of modules

The source statement is recalled here in the commutative-ring setting used by the module-valued
monoidal API.  The reusable owner keeps an exact pairing explicit, avoiding a temporary instance,
and exposes the boundedness, finite-projectivity, degreewise duality, signed differential, and
converse construction as separate declarations.

@stack 0FNK
-/

@[expose] public section

/- Lemma 15.73.2 (1): the first complex in an exact pairing of module complexes is bounded. -/
@[stacks 0FNK "(1), boundedness of the first complex"]
#check @CategoryTheory.CochainComplex.Duality.left_bounded

/- Lemma 15.73.2 (2): the second complex in an exact pairing of module complexes is bounded. -/
@[stacks 0FNK "(2), boundedness of the second complex"]
#check @CategoryTheory.CochainComplex.Duality.right_bounded

/- Lemma 15.73.2 (3): every term of the first complex is finite projective. -/
@[stacks 0FNK "(3), finite-projective terms of the first complex"]
#check @CategoryTheory.CochainComplex.Duality.left_finiteProjective

/- Lemma 15.73.2 (4): every term of the second complex is finite projective. -/
@[stacks 0FNK "(4), finite-projective terms of the second complex"]
#check @CategoryTheory.CochainComplex.Duality.right_finiteProjective

/- Lemma 15.73.2 (5): opposite homogeneous degrees inherit an exact pairing. -/
@[stacks 0FNK "(5), degreewise exact pairing"]
#check @CategoryTheory.CochainComplex.Duality.degreewise

/- Lemma 15.73.2 (6): the second complex is identified degreewise with the linear dual of the
first. -/
@[stacks 0FNK "(6), degreewise linear-dual identification"]
#check @CategoryTheory.CochainComplex.Duality.rightTermIso

/- Lemma 15.73.2 (7): under the degreewise identifications, the second differential is the
signed transpose of the first differential. -/
@[stacks 0FNK "(7), signed transpose differential"]
#check @CategoryTheory.CochainComplex.Duality.rightTermIso_d_comm

/- Lemma 15.73.2 (8): a bounded complex of finite-projective modules has its canonical dual as
an exact pairing. -/
@[stacks 0FNK "(8), canonical dual of a bounded finite-projective complex"]
#check @CochainComplex.IsBoundedFiniteProjective.exactPairingOf
