module

public import ReasLib.RingTheory.Smooth.Adic.Derivation
import StacksCheckRecall

/-!
# Lemma 15.49.1

@stack 07PL

Lemma 15.49.1 is the complete-local specialization of the reusable adic derivation-extension
theorem.  The recall retains the source Noetherian, local, and local-homomorphism assumptions.
-/

@[expose] public section

@[stacks 07PL "Lemma 15.49.1"]
#check @RingHom.exists_derivationExtension_of_completeLocal
#check @RingHom.exists_derivationExtension
