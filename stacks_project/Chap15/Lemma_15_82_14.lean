module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Tensor
import StacksCheckRecall

/-!
# Lemma 15.82.14 (067C)

@stack 067C
-/

@[expose] public section

/- Lemma 15.82.14 (1): flat extension along a pseudo-coherent ring map preserves relative
`m`-pseudo-coherence of modules over the base. -/
@[stacks 067C "(1), flat extension preserves relative m-pseudo-coherence"]
#check @CategoryTheory.ModuleCat.IsMPseudoCoherentRelativeTo.extension_of_flat_of_isPseudoCoherentRingMap

/- Lemma 15.82.14 (2): flat extension along a pseudo-coherent ring map preserves relative
pseudo-coherence of modules over the base. -/
@[stacks 067C "(2), flat extension preserves relative pseudo-coherence"]
#check @CategoryTheory.ModuleCat.IsPseudoCoherentRelativeTo.extension_of_flat_of_isPseudoCoherentRingMap
