/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Algebra structures from filtered-colimit cocones

A cocone leg in `CommRingCat` is a ring homomorphism and therefore determines
an algebra structure on the cocone point.  This neutral leaf names that
structure so filtered-colimit descent results can state tensor base changes
without rebuilding a local instance from the leg.
-/

open CategoryTheory Limits

universe u uJ vJ

namespace CommRingCat.FilteredColimit

variable {J : Type vJ} [Category.{uJ} J]

/-- The algebra structure on a cocone point induced by its `j`th leg.  It is
explicit rather than a global instance because different cocone legs give
competing algebra structures on the same target. -/
@[reducible, stacks 00U2 "filtered-colimit stage algebra"]
noncomputable def stageAlgebra
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (j : J) :
    Algebra (F.obj j) c.pt :=
  (c.ι.app j).hom.toAlgebra

/-- The scalar map of `stageAlgebra` is the selected cocone leg. -/
@[stacks 00U2 "filtered-colimit stage algebra"]
theorem stageAlgebra_algebraMap
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (j : J) :
    letI : Algebra (F.obj j) c.pt := stageAlgebra F c j
    algebraMap (F.obj j) c.pt = (c.ι.app j).hom := sorry

end CommRingCat.FilteredColimit
