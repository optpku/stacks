module

public import stacks_project.Chap77.Lemma_77_11_2
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

/- Definition 77.11.3: `ℱ` is flat over `Y` in dimensions at least `n` when the
equivalent conditions of Lemma 77.11.2 hold. -/
@[stacks 0CWT] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverInDimensionsGE ℱ f n : Prop)
