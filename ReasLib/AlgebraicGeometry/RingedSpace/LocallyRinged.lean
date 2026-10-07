module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Point
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally ringed structure from topological stalks

For the opens site of a topological space, local rings at every topological stalk imply the
site-theoretic local-unit dichotomy. This bridge belongs to ringed spaces rather than to any
particular application such as invertible modules or Picard groups.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace StalkLocalRing

/-- The structure sheaf has local unit dichotomy if all topological stalks are local rings. This
explicit form avoids installing a temporary Pi-shaped instance at call sites. -/
theorem localUnitDichotomy (X : RingedSpace.{u})
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    X.sheaf.LocalUnitDichotomy := sorry

/-- The structure sheaf of a ringed space has local unit dichotomy when all of its topological
stalks are local rings. -/
@[stacks 04ET "opens-site specialization"]
instance instLocalUnitDichotomy (X : RingedSpace.{u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    X.sheaf.LocalUnitDichotomy := sorry

/-- The structure sheaf is locally ringed if all topological stalks are local rings. This is the
explicit-assumption form of `instIsLocallyRinged`. -/
theorem isLocallyRinged (X : RingedSpace.{u})
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    X.sheaf.IsLocallyRinged := sorry

/-- The structure sheaf of a ringed space is locally ringed when all of its topological stalks
are local rings. -/
@[stacks 04H9 "opens-site specialization"]
instance instIsLocallyRinged (X : RingedSpace.{u})
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    X.sheaf.IsLocallyRinged := sorry

end StalkLocalRing

end AlgebraicGeometry.RingedSpace
