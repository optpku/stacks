/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibredness of canonical based-category wrappers

This leaf exposes the canonical fibredness instance for `BasedCategory.ofFunctor`.  Keeping the
property bridge separate lets `BasedCategory.Basic` remain independent of fibredness, while
consumers of fibred constructions avoid rebuilding the same instance locally.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- The projection of `BasedCategory.ofFunctor p` inherits the supplied fibredness of `p`.

The wrapper stores `p` definitionally.  This instance is therefore canonical; the more specific
groupoid-fibred bridge remains in `InGroupoids/Cartesian`. -/
@[stacks 02XS "fibred projection of a based-category wrapper"]
instance ofFunctor.projectionIsFibered
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    (BasedCategory.ofFunctor p).p.IsFibered := inferInstanceAs p.IsFibered

end BasedCategory

end CategoryTheory
