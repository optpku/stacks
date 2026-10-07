module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Detection.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Groupoid-fibred projection closure

This leaf owns the relative and absolute projection instances showing that
inertia preserves groupoid-fibredness.
-/

@[expose] public section

universe u v uS vS uT vT w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace RelativeInertia

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]
variable {T : Type uT} [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C}

namespace Projection

namespace Groupoids

/-- The relative-inertia projection of a cartesian functor is fibred in groupoids when its source
projection is fibred in groupoids. -/
theorem ofCartesian
    [Functor.IsFibered.InGroupoids p]
    (F : CartesianBasedFunctor p q) :
    Functor.IsFibered.InGroupoids
      (RelativeInertia.projection F.toFunctor p) := sorry

/-- Lemma 4.35.12 (Stacks 042I): the self-relative-inertia projection of a category fibred in
groupoids is again fibred in groupoids. -/
@[stacks 042I "absolute inertia projection is fibred in groupoids"]
instance self
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] :
    Functor.IsFibered.InGroupoids
      (RelativeInertia.projection p p) := sorry

end Groupoids

end Projection

end RelativeInertia

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

namespace Projection

namespace Groupoids

/-- The projection from based absolute inertia is fibred in groupoids whenever the original
projection is. -/
instance self
    (X : BasedCategory.{vS, uS} C)
    [Functor.IsFibered.InGroupoids X.p] :
    Functor.IsFibered.InGroupoids (inertia X).p := sorry

end Groupoids

end Projection

end Inertia

end BasedCategory

end CategoryTheory
