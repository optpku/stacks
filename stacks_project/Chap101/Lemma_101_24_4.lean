module

public import stacks_project.Chap101.Lemma_101_24_4_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.24.4: if `f ≫ g` is quasi-finite and `g` is quasi-separated and
quasi-DM, then `f` is quasi-finite. -/
@[stacks 0G2Q] #check
  (QuasiFinite.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiFinite (f ≫ g)] [QuasiSeparated g] [QuasiDM g],
      QuasiFinite f)
