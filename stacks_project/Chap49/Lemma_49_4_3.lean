module

import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

/- Lemma 49.4.3: for a finite flat map of Noetherian rings `A → B`, the
finite-projective trace in the relative dualizing module is a trace element. -/
@[stacks 0BT8] #check
  (Algebra.RelativeDualizingModule.finiteFlatTraceElement_isTraceElement :
    ∀ (A B : Type u) [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
      [Module.Finite A B] [Module.Flat A B],
      Algebra.RelativeDualizingModule.TraceElement.IsUniversal
        A B B (.of_moduleFinite) inferInstance
          (Algebra.RelativeDualizingModule.finiteFlatTraceElement A B))
