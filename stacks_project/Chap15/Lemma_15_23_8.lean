module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.8

@stack 0AV3

The reflexivity of finite Hom modules is owned by the shared `Module.IsReflexive` API.
-/

@[expose] public section

universe u v w

/- Lemma 15.23.8: if `M` is finite over a Noetherian domain and `N` is finite reflexive, then
`Hom_R(M, N)` is reflexive.  The owner is stated for finite presentation, which is the exact
condition used by the proof and specializes to the textbook Noetherian finite case. -/
@[stacks 0AV3 "Lemma 15.23.8"]
#check @Module.IsReflexive.linearMap_of_finitePresentation
