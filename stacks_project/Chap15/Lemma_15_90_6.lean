module
public import ReasLib.RingTheory.Sequence.Koszul.Cohomology.First
import StacksCheckRecall

/-!
# Lemma 15.90.6

@stack 05EE
-/

@[expose] public section

/-! # Lemma 15.90.6: the low-degree Ext sequence for the `05EE` Koszul object -/

/- Lemma 15.90.6, tag `05EE`: for a finite family generating `I`, the canonical sequence
`0 ⟶ Ext¹_R(R ⧸ I, N) ⟶ H₁(N, f) ⟶ Hom_R(K, N)` is left exact; here `H₁(N, f)` is the
degree-one cohomology object modeled by `KoszulComplex.Cohomology.H1`. -/
@[stacks 05EE "low-degree Ext sequence for degree-one Koszul cohomology"]
#check @KoszulComplex.Cohomology.H1.extSequence_exact

#check @KoszulComplex.Cohomology.H1.extSequence_mono
#check @KoszulComplex.Cohomology.H1.relationHomEquiv
#check @KoszulComplex.Cohomology.H1.presentationIso
