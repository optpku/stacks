module

import ReasLib.CategoryTheory.Filtration.FiniteInjective.Embedding
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.5

The shared embedding object records the filtered-injective target, the morphism, monicity, and
strictness. The chapter entry only recalls its existence and literal existential view.
-/

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.Embedding

/- Lemma 13.26.5 (`05TS`): every finite filtered object over an abelian category with enough
injectives admits a strict monomorphism into a finite filtered-injective object. -/
@[stacks 05TS] #check @nonempty

/- The source-facing formulation with separate target and morphism witnesses. -/
#check @nonempty_iff

/- The strictness projection used by later resolution constructions. -/
#check @strict

end CategoryTheory.FilteredObject.Finite.FilteredInjective.Embedding
