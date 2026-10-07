module

public import ReasLib.RingTheory.Kaehler.JacobiZariski
import StacksCheckRecall

@[expose] public section

/-!
@stack 06A7
-/

/- Lemma 10.138.11 [stacks 06A7]: canonical recall of the split
surjective Jacobi-Zariski conormal sequence for a formally smooth map. -/

@[stacks 06A7]
#check @Algebra.H1Cotangent.delta_has_section_of_formallySmooth
