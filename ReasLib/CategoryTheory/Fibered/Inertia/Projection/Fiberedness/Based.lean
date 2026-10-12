/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fiberedness.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Based absolute inertia projection fibredness

This leaf provides the based-category specializations of relative projection fibredness.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

namespace BasedCategory

namespace Inertia

namespace Projection

namespace Fibered

variable {C : Type u} [Category.{v} C]

/-- The projection from absolute inertia is fibred whenever the original based projection is
fibred. -/
@[stacks 034H "based absolute-inertia projection fibredness"]
instance self
    (X : BasedCategory.{vS, uS} C) [X.p.IsFibered] :
    (inertia X).p.IsFibered := sorry
/- Proof strategy: rewrite with `inertia_p` and apply
`CategoryTheory.RelativeInertia.Projection.Fibered.self` to `X.p`. -/

/-- The absolute-inertia projection of a raw fibred functor is fibred. This specialization makes
the canonical `BasedCategory.ofFunctor` presentation available directly to typeclass search. -/
@[stacks 034H "absolute-inertia projection fibredness for a functor"]
instance ofFunctor
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    (inertia (BasedCategory.ofFunctor p)).p.IsFibered := sorry

end Fibered

end Projection

end Inertia

end BasedCategory

end CategoryTheory
