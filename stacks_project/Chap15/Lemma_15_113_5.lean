/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tame
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.113.5

@stack 09EE

The reusable owners live in `ReasLib.FieldTheory.Galois.IntegralClosure.Tame` and
`ReasLib.RingTheory.Ideal.Cotangent.Inertia.ResidueField`.  This chapter file is a source-facing
recall block.  In particular, no quotient equivalence is chosen from a surjectivity proof: the
explicit forward map and its bijectivity are the canonical data/proposition split used downstream.
-/

/- The source notation `P` and `I_t` is represented directly by `Ideal.wildInertia` and
`Ideal.tameInertia`; no chapter aliases are exported. -/

namespace Lemma_15_113_5

/- The wild/tame inertia exact sequence is the canonical group extension
`1 ⟶ P ⟶ I ⟶ I_t ⟶ 1`. -/
@[stacks 09EE "wild-tame inertia exact sequence bridge"]
#check (@Ideal.tameExtension)

/- Lemma 15.113.5 (1): `P` is the subgroup of the decomposition group acting trivially on
every associated-graded piece `m ^ n / m ^ (n + 1)`. -/
@[stacks 09EE "Lemma 15.113.5 (1), associated-graded characterization"]
#check (@Ideal.mem_wildInertia_iff_trivial_on_associatedGraded)

/- Lemma 15.113.5 (2): wild inertia is normal in the decomposition group. -/
@[stacks 09EE "Lemma 15.113.5 (2), decomposition-group normality"]
#check (@Ideal.wildInertia_normal_in_stabilizer)

/- Lemma 15.113.5 (3): in positive residue characteristic, wild inertia is a `p`-group. -/
@[stacks 09EE "Lemma 15.113.5 (3), positive-characteristic wild inertia"]
#check (@integralClosure.Tame.wildInertia_isPGroup_of_char_ne_zero)

/- The branch and base residue characteristics agree. -/
@[stacks 09EE "base and branch residue characteristic bridge"]
#check (@integralClosure.Tame.ringChar_eq_base)

/- The characteristic-zero half of Lemma 15.113.5 (3). -/
@[stacks 09EE "wild inertia characteristic-zero bridge"]
#check (@integralClosure.Tame.wildInertia_eq_bot_of_char_zero)

/- The cyclicity clause in Lemma 15.113.5 (4). -/
@[stacks 09EE "cyclic tame inertia bridge"]
#check (@integralClosure.Tame.tameInertia_isCyclic)

/- Lemma 15.113.5 (4): tame inertia has order equal to the prime-to-`p` part of `e`. -/
@[stacks 09EE "Lemma 15.113.5 (4), tame ramification order"]
#check (@integralClosure.Tame.tameInertiaCard_eq_ordCompl_ramificationIdx)

/- Lemma 15.113.5 (5): the explicit quotient map from tame inertia to `μ_e(κ(m))`. -/
@[stacks 09EE "Lemma 15.113.5 (5), canonical tame character"]
#check (@integralClosure.Tame.quotientHom)

/- The inertia-level character induced by the quotient map. -/
@[stacks 09EE "tame inertia character"]
#check (@integralClosure.Tame.character)

/- Lemma 15.113.5: the quotient map agrees with the tame character on inertia classes. -/
@[stacks 09EE "tame inertia quotient map on classes"]
#check (@integralClosure.Tame.quotientHom_mk)

/- The tame inertia character has wild inertia as its kernel. -/
@[stacks 09EE "tame inertia character kernel"]
#check (@integralClosure.Tame.character_ker)

/- The tame inertia character is surjective. -/
@[stacks 09EE "tame inertia character surjectivity"]
#check (@integralClosure.Tame.character_surjective)

/- The map in Lemma 15.113.5 (5) is bijective, without choosing a noncanonical inverse. -/
@[stacks 09EE "tame inertia quotient canonical identification"]
#check (@integralClosure.Tame.quotientHom_bijective)

/- Lemma 15.113.5 (6): if the residue extension is separable, wild inertia is exactly the
subgroup acting trivially modulo `m ^ 2`. -/
@[stacks 09EE "Lemma 15.113.5 (6), mod-square characterization"]
#check (@integralClosure.Tame.modSquareInertia_eq_wildInertia_of_isSeparable)

/- The cotangent representation is the degree-one form of clause (1). -/
@[stacks 09EE "wild inertia cotangent-kernel bridge"]
#check (@Ideal.Cotangent.inertiaRepresentation_ker)

/- The quotient map has the residue determinant as its underlying unit on every inertia class. -/
@[stacks 09EE "tame inertia determinant class formula"]
#check (@Ideal.Cotangent.tameResidueDet_mk)

end Lemma_15_113_5
