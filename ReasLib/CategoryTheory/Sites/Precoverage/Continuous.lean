/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
# Continuity for precoverage-presented sites

The bundled condition here is the source-facing version of continuity for sites given by
precoverages.  It records preservation of covers and of the pullbacks that occur in them.
-/

@[expose] public section

open CategoryTheory Limits

universe uC uD vC vD

namespace CategoryTheory.Functor.Precoverage

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A functor between precoverage-presented sites preserves covering families and their induced
pullbacks. -/
@[stacks 00WV "continuous functor of precoverages"]
class IsContinuous
    (u : C ⥤ D) (J : _root_.CategoryTheory.Precoverage C)
    (K : _root_.CategoryTheory.Precoverage D) : Prop where
  /-- Covering families are preserved by the precoverage comap. -/
  toLeComap : J ≤ K.comap u
  /-- Pullbacks along members of a covering family are preserved. -/
  preservesPullback
    {V : C} {R : Presieve V} (hR : R ∈ J V) {Y : C} {i : Y ⟶ V} (hi : R i)
    {T : C} (f : T ⟶ V) [HasPullback f i] :
    PreservesLimit (cospan f i) u

namespace IsContinuous

variable {J : _root_.CategoryTheory.Precoverage C}
variable {K : _root_.CategoryTheory.Precoverage D} {u : C ⥤ D}

/-- A functor continuous for Grothendieck topologies and preserving pullbacks determines the
corresponding selected-precoverage continuity datum.  This is deliberately not an instance, so
it cannot form a search loop with passage from precoverages to generated topologies. -/
@[stacks 00WV "Grothendieck-to-precoverage continuity bridge"]
theorem ofGrothendieck
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [PreservesLimitsOfShape WalkingCospan u] :
    IsContinuous u J.toPrecoverage K.toPrecoverage := sorry

/-- Under the ambient pullback hypothesis, source-facing continuity supplies Mathlib's
`Precoverage.PullbacksPreservedBy` owner. -/
theorem pullbacksPreservedBy [J.HasPullbacks] (h : IsContinuous u J K) :
    J.PullbacksPreservedBy u := sorry

/-- A continuous functor of precoverage-presented sites preserves covers after passage to the
associated Grothendieck topologies. -/
theorem coverPreserving
    [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] [J.HasPullbacks]
    (h : IsContinuous u J K) :
    CoverPreserving J.toGrothendieck K.toGrothendieck u := sorry

/-- The induced functor is continuous for the Grothendieck topologies associated to sufficiently
stable precoverages. -/
instance toGrothendieck
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.IsStableUnderBaseChange] [K.HasPullbacks]
    [IsContinuous u J K] :
    u.IsContinuous J.toGrothendieck K.toGrothendieck := sorry

/-- The identity functor is continuous for every precoverage. -/
instance id (J : _root_.CategoryTheory.Precoverage C) :
    IsContinuous (𝟭 C) J J := sorry

end IsContinuous

end CategoryTheory.Functor.Precoverage
