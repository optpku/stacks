module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tame
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.113.6

@stack 0BU4

This entry only fixes terminology for the canonical wild inertia subgroup, tame inertia quotient,
and tame inertia character constructed in Lemma 15.113.5.  The reusable owners are recalled
directly; no chapter-specific aliases or selected inverse are introduced.
-/

namespace Definition_15_113_6

/- Definition 15.113.6 (1): wild inertia is the cotangent-kernel subgroup. -/
@[stacks 0BU4 "Definition 15.113.6 (1): wild inertia group"]
#check (@Ideal.wildInertia)

/- Definition 15.113.6 (2): tame inertia is inertia modulo wild inertia. -/
@[stacks 0BU4 "Definition 15.113.6 (2): tame inertia group"]
#check (@Ideal.tameInertia)

/- Definition 15.113.6 (3): the canonical projection belongs to the wild/tame exact sequence. -/
@[stacks 0BU4 "Definition 15.113.6 (3): tame inertia projection"]
#check (@Ideal.tameExtension)

/- Definition 15.113.6 (4): the tame inertia character on inertia. -/
@[stacks 0BU4 "Definition 15.113.6 (4): tame inertia character"]
#check (@integralClosure.Tame.character)

/- Definition 15.113.6 (5): the explicit character induced on the tame quotient. -/
@[stacks 0BU4 "Definition 15.113.6 (5): tame quotient character"]
#check (@integralClosure.Tame.quotientHom)

/- Definition 15.113.6 (6): wild inertia is the kernel of the character. -/
@[stacks 0BU4 "Definition 15.113.6 (6): tame character kernel"]
#check (@integralClosure.Tame.character_ker)

/- Definition 15.113.6 (7): the character is surjective. -/
@[stacks 0BU4 "Definition 15.113.6 (7): tame character surjectivity"]
#check (@integralClosure.Tame.character_surjective)

/- Definition 15.113.6 (8): the quotient character is the canonical forward bijection. -/
@[stacks 0BU4 "Definition 15.113.6 (8): tame quotient identification"]
#check (@integralClosure.Tame.quotientHom_bijective)

end Definition_15_113_6
