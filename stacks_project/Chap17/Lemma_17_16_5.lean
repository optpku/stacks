module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

/- Lemma 17.16.5: for any `𝒪_X`-module `F`, the functor `G ↦ F ⊗ G` on `Mod(𝒪_X)`
commutes with arbitrary colimits. -/
@[stacks 05NB]
#check fun {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (F : C) [Closed F] =>
  (inferInstance : PreservesColimits (tensorLeft F))
