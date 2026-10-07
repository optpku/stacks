module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Functor.IsAlmostCocontinuous

/- Lemma 18.15.3 (04BD) (1): almost cocontinuous pushforward is exact on additive sheaves. -/
@[stacks 04BD "(1)"]
#check @pushforwardContinuous_exact

/- Lemma 18.15.3 (04BD) (2): the corresponding pushforward of module sheaves is exact. -/
@[stacks 04BD "(2)"]
#check @sheafOfModules_pushforward_exact
