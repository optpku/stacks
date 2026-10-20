module

public import ReasLib.RingTheory.Etale.FinitePresentation
import StacksCheckRecall

/-!
@stack 00UR

# Formally Etale Maps of Finite Presentation

Lemma 10.150.3 is recalled through the canonical map-first criterion in
`ReasLib.RingTheory.Etale.FinitePresentation`.
-/

@[expose] public section

/- Lemma 10.150.3: a finitely presented ring map is formally etale if and only
if it is etale. -/
@[stacks 00UR "finite-presentation criterion"]
#check @RingHom.formallyEtale_iff_etale
#print axioms RingHom.formallyEtale_iff_etale
