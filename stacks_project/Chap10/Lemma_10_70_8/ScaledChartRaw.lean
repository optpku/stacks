module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Scaling
import StacksCheckRecall

/-!
# Lemma 10.70.8 scaled chart recall

The cast-sensitive raw chart presentation has no independent downstream
meaning.  The named ReasLib scaling map is the stable owner.
-/

@[expose] public section

/- Lemma 10.70.8 (0BBI): recall the underlying ring map and its canonical
`R`-algebra refinement. -/
@[stacks 0BBI] #check @AffineBlowupChart.Scaling.toRingHom
#check @AffineBlowupChart.Scaling.toRingHom_algebraMap
#check @AffineBlowupChart.Scaling.map
