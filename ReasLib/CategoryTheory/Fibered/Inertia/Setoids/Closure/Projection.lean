/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InSetoids
public import ReasLib.CategoryTheory.Fibered.Inertia.Faithful
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Closure.Projection
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Setoids.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred projection closure

This leaf owns the relative and absolute projection instances showing that
inertia preserves setoid-fibredness.
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

namespace Faithful

/-- A relative-inertia projection is faithful whenever the source projection is faithful. -/
instance ofFaithful
    (F : S ⥤ T) (p : S ⥤ C) [p.Faithful] :
    (RelativeInertia.projection F p).Faithful := sorry
/- Proof strategy: equality after applying the relative-inertia projection gives equality of the
underlying arrows by faithfulness of `p`; conclude with `RelativeInertia.hom_ext`. -/

end Faithful

namespace Setoids

/-- The relative-inertia projection of a cartesian functor is fibred in setoids when its source
projection is fibred in setoids. -/
theorem ofCartesian
    [Functor.IsFibered.InSetoids p]
    (F : CartesianBasedFunctor p q) :
    Functor.IsFibered.InSetoids
      (RelativeInertia.projection F.toFunctor p) := sorry
/- Proof strategy: use `RelativeInertia.Projection.Groupoids.ofCartesian F` for the
groupoid-valued superclass and `RelativeInertia.Projection.Faithful.ofFaithful F.toFunctor p` for
faithfulness, then apply
`IsFibered.InSetoids.iff_inGroupoids_faithful`. -/

/-- The self-relative-inertia projection of a category fibred in setoids is again fibred in
setoids. -/
instance self
    (p : S ⥤ C) [Functor.IsFibered.InSetoids p] :
    Functor.IsFibered.InSetoids
      (RelativeInertia.projection p p) := sorry
/- Proof strategy: specialize `ofCartesian` to the identity cartesian based
functor. -/

end Setoids

end Projection

end RelativeInertia

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

namespace Projection

namespace Setoids

/-- The projection from based absolute inertia is fibred in setoids whenever the original
projection is. -/
instance self
    (X : BasedCategory.{vS, uS} C)
    [Functor.IsFibered.InSetoids X.p] :
    Functor.IsFibered.InSetoids (inertia X).p := sorry
/- Proof strategy: rewrite with `BasedCategory.inertia_p` and use
`RelativeInertia.Projection.Setoids.self`. -/

end Setoids

end Projection

end Inertia

end BasedCategory

end CategoryTheory
