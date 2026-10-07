module

public import ReasLib.CategoryTheory.Fibered.Split
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transporting split fibredness across strict isomorphisms

This leaf records the property-level transport of a splitting along a strict isomorphism of
categories over a common base. Explicit `SplitCleavage` data remains the owner of a chosen
splitting; this theorem deliberately transports only the existence property.
-/

@[expose] public section

universe v u vX uX vY uY

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

namespace BasedCategory.StrictIso

/-- Split fibredness is invariant under a strict isomorphism of categories over the same base.

The result is deliberately a theorem, rather than an instance: a strict isomorphism is explicit
comparison data and typeclass search should not choose one merely to transport a property. -/
@[stacks 02XW "split fibredness invariant under strict isomorphism over the base"]
theorem isFiberedSplit_iff (e : BasedCategory.StrictIso X Y) :
    Functor.IsFibered.Split X.p ↔ Functor.IsFibered.Split Y.p := sorry
/- Proof strategy: transport a selected `SplitCleavage` along the strict inverse functors of `e`.
The strict projection equations identify every displayed base arrow, while the unit and counit
are vertical isomorphisms; the selected lift laws transfer across those vertical isomorphisms. -/

end BasedCategory.StrictIso

end CategoryTheory
