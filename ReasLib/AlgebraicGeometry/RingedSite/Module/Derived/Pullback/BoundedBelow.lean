/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Flat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-below derived pullback on ringed-site modules

Flat pullback is already an exact functor on module sheaves.  This leaf only
records its canonical restriction to bounded-below derived categories; the
cohomology-in restriction is owned by the neighboring `CohomologyIn` leaf.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- The bounded-below derived pullback of a flat morphism of ringed sites. -/
@[stacks 015A "bounded-below derived pullback on modules"]
noncomputable abbrev modulePullbackDerivedPlus
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [(f.modulePushforward.{z}).IsRightAdjoint] [IsFlat.{z} f] :
    DerivedCategory.Plus (ModuleCat.{z} Y) ⥤
      DerivedCategory.Plus (ModuleCat.{z} X) :=
  ExactFunctor.Derived.Plus.functor (IsFlat.exactPullback.{z} f)

end RingedSite.Hom

end
