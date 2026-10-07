module

public import ReasLib.Topology.Sheaves.Types.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace

universe u

variable {X : TopCat} (ℱ : TopCat.Sheaf (Type u) X) (U : Opens X)

/- Lemma 6.11.1: for every open subset `U` of `X`, the canonical map from sections of `ℱ` on
`U` to the family of stalks `(ℱ_x)_{x ∈ U}` is injective. -/
@[stacks 0079]
#check TopCat.Presheaf.sectionToStalkFamily_injective ℱ U
