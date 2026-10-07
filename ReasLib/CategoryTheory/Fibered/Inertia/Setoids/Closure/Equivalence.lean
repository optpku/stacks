module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.InSetoids
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Forget.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Faithful
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred inertia equivalence closure

This leaf owns the equivalence characterizations for relative, based, and
heterogeneous absolute-inertia forgetting.
-/

@[expose] public section

universe u v uS vS uY vY

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace RelativeInertia

namespace forget

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

/-- For a category fibred in groupoids, forgetting the automorphism from absolute inertia is an
equivalence exactly when the original projection is fibred in setoids. -/
@[stacks 042J]
theorem isEquivalence_iff_inSetoids
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] :
    (RelativeInertia.forget p).IsEquivalence ↔
      Functor.IsFibered.InSetoids p := sorry
/- Proof strategy: if the forgetful functor is an equivalence, fullness applied between the
identity and a chosen automorphism forces every fibre automorphism to be the identity, so use
`IsFibered.InSetoids.iff_inGroupoids_fibersSubsingletonAut`.  Conversely thin fibres identify
every inertia automorphism with the identity; the identity section is then a quasi-inverse. -/

end forget

end RelativeInertia

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

namespace forget

/-- For a based category fibred in groupoids, its absolute-inertia forgetful based functor is an
equivalence over the base exactly when its projection is fibred in setoids. -/
@[stacks 042J "based category form"]
theorem isEquivalence_iff_inSetoids
    (X : BasedCategory.{vS, uS} C)
    [Functor.IsFibered.InGroupoids X.p] :
    (BasedCategory.Inertia.forget X).IsEquivalence ↔
      Functor.IsFibered.InSetoids X.p := sorry
/- Proof strategy: forget the based equivalence to obtain an equivalence of total categories and
apply `RelativeInertia.forget.isEquivalence_iff_inSetoids`. In the reverse direction, package the
identity section and the fibrewise identity of all inertia automorphisms as a based quasi-inverse. -/

end forget

namespace cartesianForget

/-- For a category fibred in groupoids, heterogeneous cartesian inertia forgetting is an
equivalence exactly when the original projection is fibred in setoids. -/
@[stacks 042J "heterogeneous cartesian based category form"]
theorem isEquivalence_iff_inSetoids
    (X : BasedCategory.{vS, uS} C)
    [Functor.IsFibered.InGroupoids X.p] :
    (BasedCategory.Inertia.cartesianForget X).toBasedFunctor.IsEquivalence ↔
      Functor.IsFibered.InSetoids X.p := sorry

end cartesianForget

end Inertia

end BasedCategory

end CategoryTheory
