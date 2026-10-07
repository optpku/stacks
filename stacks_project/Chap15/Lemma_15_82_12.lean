module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.TorIndependent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.82.12 (067A)

Let `R → A` be finite type, let `K` be (m-)pseudo-coherent relative to `R`, and let `R → R'`
make `A` and `R'` Tor independent over `R`.  With `A' = A ⊗[R] R'`, the derived base change of
`K` is (m-)pseudo-coherent relative to `R'`.  The reusable owner is
`CategoryTheory.DerivedCategory.torIndependentBaseChange` and its two Prop statements.

@stack 067A
-/

@[stacks 067A "Lemma 15.82.12 (1)"]
#check @CategoryTheory.DerivedCategory.isMPseudoCoherentRelativeTo_torIndependentBaseChange

@[stacks 067A "Lemma 15.82.12 (2)"]
#check @CategoryTheory.DerivedCategory.isPseudoCoherentRelativeTo_torIndependentBaseChange
