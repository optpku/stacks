module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Limit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential derived limits and pushforward on ringed spaces

This file exposes the ringed-space specialization of the generic ringed-site preservation theorem.
The additive, Grothendieck, countable-product, and `AB4*` hypotheses are canonical instances and do
not appear as ambient parameters in the public interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.moduleDerivedPushforward

/-- Derived direct image on a ringed space preserves sequential derived limits.  Since
`IsDerivedLimit` contains presentation data, the canonical statement records existence rather
than choosing a presentation in the public API. -/
@[stacks 0BKP "derived pushforward preserves sequential derived limits"]
theorem preservesDerivedLimit {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    {Ksys : SequentialInverseSystem (ModuleDerived X)} {K : ModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    Nonempty (IsDerivedLimit
      (Ksys ⋙ moduleDerivedPushforward f)
      ((moduleDerivedPushforward f).obj K)) := sorry

end AlgebraicGeometry.RingedSpace.moduleDerivedPushforward

end
