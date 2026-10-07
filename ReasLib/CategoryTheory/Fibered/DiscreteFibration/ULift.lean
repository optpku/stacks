module

public import ReasLib.CategoryTheory.Category.ULift
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete fibrations from categorical universe lifts

The canonical universe-down functors are discrete fibrations.  Keeping these facts with the
intrinsic discrete-fibration owner lets downstream resized constructions inherit fiberedness by
composition.
-/

@[expose] public section

universe u v w v'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Cat.ObjULift

/-- The canonical functor forgetting the bundled object-universe lift is a discrete fibration. -/
@[stacks 02XS "discrete-fibration API for the bundled object-universe lift"]
instance down.isDiscreteFibration (C : Type u) [Category.{v} C] :
    Functor.IsDiscreteFibration (down.{u, v, w} C) := sorry

end Cat.ObjULift

namespace Cat.TwoULift

/-- The canonical functor forgetting the bundled object and morphism universe lifts is a discrete
fibration. -/
@[stacks 0046 "discrete-fibration API for the bundled two-universe lift"]
instance down.isDiscreteFibration (C : Type u) [Category.{v} C] :
    Functor.IsDiscreteFibration (down.{u, v, w, v'} C) := sorry

end Cat.TwoULift

/-- The morphism-universe down functor is a discrete fibration. -/
instance ULiftHom.down.isDiscreteFibration :
    Functor.IsDiscreteFibration
      (ULiftHom.down : ULiftHom.{w} C ⥤ C) := sorry

end CategoryTheory
