module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.FiniteModule
import StacksCheckRecall

/-!
# Lemma 15.95.5

@stack 09BA

The ordinary-completeness and finite-generation conclusions are owned by the reusable
derived-completion leaf.
-/

@[expose] public section

noncomputable section

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {I : Ideal A} {M : ModuleCat A}

-- Local instance justification (instance diamond): expose the canonical
-- completed-ring action only while checking the two completed-module conclusions.
attribute [local instance] IsAdicComplete.completedModule

section

variable [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))]

/- Lemma 15.95.5 (1): finite reduction of a derived-complete module implies ordinary adic
completeness. -/
@[stacks 09BA "Lemma 15.95.5 (1)"]
#check fun (hM : M.IsDerivedCompleteWithRespectTo I) ↦
  (ModuleCat.IsDerivedCompleteWithRespectTo.isAdicComplete_of_finite_quotient hM :
    IsAdicComplete I M)

/- Lemma 15.95.5 (2): the module is finite over the completed coefficient ring. -/
@[stacks 09BA "Lemma 15.95.5 (2)"]
#check fun (hM : M.IsDerivedCompleteWithRespectTo I) ↦
  (ModuleCat.IsDerivedCompleteWithRespectTo.moduleFinite_over_adicCompletion_of_finite_quotient
      hM :
    let _ : IsAdicComplete I M :=
      ModuleCat.IsDerivedCompleteWithRespectTo.isAdicComplete_of_finite_quotient hM
    Module.Finite (AdicCompletion I A) M)

/- The ordinary completion of the module is finite over the completed ring under the same
hypotheses. -/
#check fun (hM : M.IsDerivedCompleteWithRespectTo I) ↦
  (ModuleCat.IsDerivedCompleteWithRespectTo.moduleFinite_adicCompletion_of_finite_quotient hM :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M))

end

/- The core finite-generation theorem for an already adically complete module. -/
section

variable [IsAdicComplete I M]
variable [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))]

#check (IsAdicComplete.moduleFinite_of_finite_quotient :
  Module.Finite (AdicCompletion I A) M)

end
