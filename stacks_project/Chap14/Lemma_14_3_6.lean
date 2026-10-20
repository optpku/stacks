module

public import ReasLib.AlgebraicTopology.SimplicialObject.Split
import StacksCheckRecall

/-!
@stack 016F
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 1))

/- Lemma 14.3.6: every degeneracy morphism of a simplicial object is a split monomorphism. -/
@[stacks 016F]
#check (SimplicialObject.σ.splitMono U i : SplitMono (U.σ i))

#check (inferInstance : IsSplitMono (U.σ i))
#check (inferInstance : Mono (U.σ i))
