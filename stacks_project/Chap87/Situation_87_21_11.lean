module

public import stacks_project.Chap87.Situation_87_21_11_Composition
import StacksCheckRecall

@[expose] public section

open TopologicalRing

/- Situation 87.21.11: let P be a local property of morphisms of WAdm^count in
the sense of Situation 87.21.2. Then P is stable under composition if continuous
φ : B →+* A and ψ : C →+* B in WAdm^count with P φ and P ψ imply P (φ.comp ψ). -/
@[stacks 0GBH] #check TopologicalRing.IsStableUnderComposition
