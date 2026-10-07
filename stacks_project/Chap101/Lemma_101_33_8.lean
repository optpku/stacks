module

public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_28_8
public import stacks_project.Chap103.«103_15_1_1_Smooth»
import StacksCheckRecall

/-!
# Gerbes are surjective and smooth

A morphism of algebraic stacks that makes the source a gerbe over the target
is surjective and smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.33.8 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `f` is `Surjective`. -/
@[stacks 0DN8] #check
  (Surjective.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f],
      Surjective f)

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- Lemma 101.33.8 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `X` is a gerbe over `Y`, then `f` is `Smooth`. -/
@[stacks 0DN8]
instance of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f] :
    Smooth f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
