module

public import stacks_project.Chap106.Lemma_106_5_1_Flat
public import stacks_project.Chap106.Lemma_106_5_1_FlatAt
import StacksCheckRecall

/-!
# Flatness of morphisms of thickenings of algebraic stacks
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicStack.IsThickening

/- Lemma 106.5.1 (1): in a 2-commutative triangle of thickenings of algebraic
stacks, with Y' ⟶ B' locally of finite type, X' ⟶ B' flat and locally of finite
presentation, f flat, and both vertical squares 2-fibre products, f' is flat. -/
@[stacks 0CJB] #check flatAmbient

/- Lemma 106.5.1 (2): under the same hypotheses, Y' ⟶ B' is flat at every point
of |Y'| in the image of |f'|. -/
@[stacks 0CJB] #check flatAtTarget
