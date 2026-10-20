module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Point
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived internal Hom on stalks

The derived stalk comparison is the canonical internal-Hom comparison for derived pullback along
the point inclusion.  Its flatness is canonical and is inferred from the point.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.Stalk

variable {X : RingedSpace.{u}} (x : X)
variable [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived (pointRingedSpace x))]
variable [MonoidalClosed (ModuleDerived (pointRingedSpace x))]
variable [(modulePullbackDerived (pointInclusion x)).Monoidal]

/-- The canonical point-inclusion model for the comparison from the stalk of a derived internal
Hom to the derived internal Hom of the stalks. -/
@[stacks 0GM8 "canonical stalk comparison"]
noncomputable abbrev comparison (K M : ModuleDerived X) :=
  modulePullbackDerived.InternalHom.comparison (pointInclusion x) K M

/-- Lemma 20.51.4 (1): the derived internal-Hom stalk comparison is an isomorphism when its
first argument is perfect. -/
@[stacks 0GM8 "(1)"]
theorem isIso_of_isPerfect {K M : ModuleDerived X}
    (hK : ModuleDerived.IsPerfect K) :
    IsIso (comparison x K M) := sorry

/-- Lemma 20.51.4 (2): the derived internal-Hom stalk comparison is an isomorphism from a
pseudo-coherent object into a locally bounded-below object. -/
@[stacks 0GM8 "(2)"]
theorem isIso_of_isPseudoCoherent {K M : ModuleDerived X}
    (hK : ModuleDerived.IsPseudoCoherent K)
    (hM : ModuleDerived.IsLocallyBoundedBelow M) :
    IsIso (comparison x K M) := sorry

end AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.Stalk
