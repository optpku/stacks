module

public import stacks_project.Chap67.Lemma_67_8_9_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.8.9: if `f ≫ g` is quasi-compact and `g` is quasi-separated, then
`f` is quasi-compact. -/
@[stacks 03KS] #check
  (QuasiCompact.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiCompact (f ≫ g)] [QuasiSeparated g],
      QuasiCompact f)
