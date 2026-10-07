module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.InternalHom.Stalk
import StacksCheckRecall

@[expose] public section

/-
Lemma 20.51.4 (1) (0GM8): for a perfect first argument, recall the canonical derived
internal-Hom comparison on the stalk at a point.
-/
@[stacks 0GM8 "(1)"]
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.Stalk.isIso_of_isPerfect

/-
Lemma 20.51.4 (2) (0GM8): for a pseudo-coherent first argument and a locally bounded-below
second argument, recall the same canonical stalk comparison.
-/
@[stacks 0GM8 "(2)"]
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.Stalk.isIso_of_isPseudoCoherent

-- The source-facing comparison and its canonical flatness input remain independently reusable.
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.Stalk.comparison
#check @AlgebraicGeometry.pointInclusion_isFlat
