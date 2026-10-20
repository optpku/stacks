module

public import ReasLib.Algebra.Module.Length
import StacksCheckRecall

/-!
# Finite length from annihilation

Lemma 10.52.8 gives finite length for a finite module killed by a power of a finitely generated
maximal ideal.

@stack 00J0
-/

@[expose] public section

/- Lemma 10.52.8 (Tag 00J0): the chapter's annihilation criterion is recalled from the
canonical `Module.isFiniteLength_of_pow_smul_top_eq_bot` owner.  The owner uses `IsFiniteLength`
directly and names the acted-on top submodule explicitly; no duplicate root-level alias is kept. -/
@[stacks 00J0]
#check @Module.isFiniteLength_of_pow_smul_top_eq_bot

section SourceSpecialization

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (m : Ideal R) [m.IsMaximal] [Module.Finite R M]

/- The source assumptions are exactly the owner assumptions specialized to a maximal ideal. -/
@[stacks 00J0]
#check Module.isFiniteLength_of_pow_smul_top_eq_bot (m := m)

end SourceSpecialization
