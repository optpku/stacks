module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.45.5

Pseudo-coherence under derived tensor product is owned for arbitrary bundled ringed sites in
`RingedSite.Hom.ModuleDerived`.  This source entry checks both clauses of the Stacks lemma against
that shared API.
-/

/- Lemma 21.45.5 (1) (09J9): bounded pseudo-coherence degrees add under derived tensor product. -/
@[stacks 09J9 "(1)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.tensor

/- Lemma 21.45.5 (2) (09J9): the derived tensor product of pseudo-coherent objects is
pseudo-coherent. -/
@[stacks 09J9 "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsPseudoCoherent.tensor

end
