/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree

@[expose] public section
open TopologicalSpace
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Modules
/-- The union of the open subsets on which a scheme module is free. -/
def freeLocus {X : Scheme.{u}} (F : X.Modules) : X.Opens :=
  sSup {U : X.Opens | SheafOfModules.IsFree (F.over U)}
/-- A point belongs to the free locus exactly when the module is free on some open neighborhood. -/
theorem mem_freeLocus_iff {X : Scheme.{u}} (F : X.Modules) (x : X) :
    x ∈ freeLocus F ↔ ∃ (U : X.Opens) (_ : x ∈ U) (I : Type u),
      Nonempty (F.over U ≅ SheafOfModules.free I) := sorry
end AlgebraicGeometry.Scheme.Modules
