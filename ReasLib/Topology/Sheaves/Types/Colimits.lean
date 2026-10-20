/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Limits

/-!
# Colimits of Type-valued sheaves

Mathlib owns the generic sheaf-colimit instances. Since `TopCat.Sheaf` is a
definition rather than an abbreviation, this module exposes the two useful
same-universe instances through that representation boundary.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- The Mathlib same-universe coproduct instance, exposed through `TopCat.Sheaf`. -/
noncomputable instance hasTypeIndexedCoproducts (I : Type u) :
    HasColimitsOfShape (Discrete I) (TopCat.Sheaf (Type u) X) :=
  (inferInstance : HasColimitsOfShape (Discrete I)
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)))

/-- The Mathlib same-universe coequalizer instance, exposed through `TopCat.Sheaf`. -/
noncomputable instance hasTypeCoequalizers :
    HasColimitsOfShape WalkingParallelPair (TopCat.Sheaf (Type u) X) :=
  (inferInstance : HasColimitsOfShape WalkingParallelPair
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)))

#synth HasColimitsOfShape (Discrete (ULift.{u} PUnit)) (TopCat.Sheaf (Type u) X)
#synth HasColimitsOfShape WalkingParallelPair (TopCat.Sheaf (Type u) X)

end TopCat.Sheaf
