module

public import ReasLib.CategoryTheory.Category.Pointed.Limits
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Kernel
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointed sections supported on a closed subset

For pointed sheaves, vanishing means equality with the distinguished point. This file identifies
the coefficient-generic kernel inclusion with that sectionwise condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

variable {X : TopCat.{u}} {Z : Set X}

/-- Remark 17.6.4 (01B0): a local section of a pointed sheaf is supported on `Z` when its
restriction to the open complement is the distinguished point. -/
@[stacks 01B0 "pointed section supported on a closed subset"]
def IsSupported
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) (U : Opens X)
    (s : F.presheaf.obj (op U)) : Prop :=
  F.presheaf.map (Opens.infLELeft U (openComplement hZ)).op s =
    (F.presheaf.obj (op (U ⊓ openComplement hZ))).point

/-- The image of the ambient kernel inclusion consists exactly of the pointed sections supported
on `Z`. -/
@[stacks 01B0 "kernel description of pointed sections with support"]
theorem mem_range_inclusion_app_iff
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    s ∈ Set.range ((inclusion hZ F).1.app (op U)) ↔ IsSupported hZ F U s := sorry

/-- The subobject view of the ambient kernel has the same sectionwise support criterion. -/
theorem mem_range_subsheaf_arrow_app_iff
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    s ∈ Set.range ((subsheaf hZ F).arrow.1.app (op U)) ↔
      IsSupported hZ F U s := sorry

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

end
