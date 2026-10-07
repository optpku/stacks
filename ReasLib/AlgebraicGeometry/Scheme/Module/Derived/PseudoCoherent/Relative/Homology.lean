module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.BoundedAbove
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative pseudo-coherence from homology

This file gives a homological criterion for relative pseudo-coherence of locally bounded-above
derived modules on schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace IsMPseudoCoherentOver

/-- A locally bounded-above derived module is relatively `m`-pseudo-coherent when its homology
in every degree `i` is relatively `(m - i)`-pseudo-coherent. -/
@[stacks 09UQ]
theorem of_homology {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ)
    (hE : E.IsLocallyBoundedAbove)
    (hH : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsMPseudoCoherentOver f (m - i)) :
    IsMPseudoCoherentOver f E m := sorry

end IsMPseudoCoherentOver
end ModuleDerived
end Scheme
end AlgebraicGeometry
