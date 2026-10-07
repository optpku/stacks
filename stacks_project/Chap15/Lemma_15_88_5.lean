module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Sequential.Realization
import StacksCheckRecall

/-!
# Lemma 15.88.5

@stack 091I
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.88.5 (091I): a compatible family `K_n ∈ D(A_n)` and transition morphisms
`K_{n + 1} ⟶ K_n` viewed after restriction of scalars is realized by one object of the derived
category of varying-ring modules, with compatible stagewise isomorphisms. -/
@[stacks 091I]
#check @ModuleCat.DerivedTower.existsRealization

#check @ModuleCat.DerivedTower.Realization
#check @ModuleCat.DerivedTower.ofCochainComplex

end
