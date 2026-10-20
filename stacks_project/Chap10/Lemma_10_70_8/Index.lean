module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Scaling
import StacksCheckRecall

/-!
# Lemma 10.70.8 index

Compatibility imports for this chapter item resolve directly to the shared
scaling owner.
-/

@[expose] public section

/- Lemma 10.70.8 (0BBI): canonical scaling-map owner. -/
@[stacks 0BBI] #check @AffineBlowupChart.Scaling.map
