module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.InheritedTopology

/-!
# The inherited topology on a slice projection

The topology inherited by the projection `Over.forget U` is the ordinary slice topology.
Keeping this comparison next to the general inherited-topology construction prevents stack
consumers from rebuilding it through a presentation by covering families.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Functor.inheritedTopology

/-- The topology inherited from `(C, J)` by the slice projection `C/U ⟶ C` is `J.over U`. -/
@[stacks 06NV "inherited topology of a slice projection", simp]
theorem overForget
    (J : GrothendieckTopology C) (U : C) :
    (Over.forget U).inheritedTopology J = J.over U := sorry

end Functor.inheritedTopology

end CategoryTheory
