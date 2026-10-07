module

public import ReasLib.Topology.Sheaves.Basis.Types.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

variable {X : TopCat.{u}} {B : Set (Opens X)}
variable (hB : Opens.IsBasis B)

/- Lemma 6.30.7: restriction from sheaves of sets on `X` to sheaves on the topological basis `B`
is an equivalence of categories. -/
@[stacks 009O]
#check (BasisSheaf.restriction_isEquivalence (X := X) hB)
