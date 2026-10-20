module

public import ReasLib.RingTheory.Ideal.Nakayama.Localization
import StacksCheckRecall

/-!
# Clearing generators after localization

@stack 0GLX

Lemma 10.20.2 is the finite-family specialization of the unrestricted
quotient-span localization criterion recalled below.
-/

@[expose] public section

@[stacks 0GLX "canonical submodule criterion"]
#check @Submodule.exists_mem_add_ideal_and_smul_top_le_of_quotient_localized_eq_top

@[stacks 0GLX "finite-family span source view"]
#check @Submodule.exists_mem_add_ideal_and_span_localized_eq_top_of_quotient_span_localized_eq_top
