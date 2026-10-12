/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom.FiniteDescent

/-- For a proper scheme of dimension at most one over a field, a finite morphism
that is a closed immersion over a dense open does not increase the first
structure-sheaf cohomology finrank. -/
theorem structureSheafH1Finrank_le
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : Y ⟶ X) [IsFinite f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hU : ∃ U : X.Opens, Dense (U : Set X) ∧ IsClosedImmersion (f ∣_ U)) :
    Scheme.Hom.cohomologyFinrank (f ≫ p)
        (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) 1 ≤
      Scheme.Hom.cohomologyFinrank p
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1 := sorry

end Scheme.Hom.FiniteDescent
end AlgebraicGeometry
