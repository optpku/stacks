/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiniteDescent

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom.ProperBirational

/-- A proper birational morphism onto a proper scheme of dimension at most one
does not increase the first structure-sheaf cohomology finrank. -/
theorem structureSheafH1Finrank_le
    {k : Type u} [Field k] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X' ⟶ X) [IsBirational f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) :
    Scheme.Hom.cohomologyFinrank (f ≫ p)
        (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) 1 ≤
      Scheme.Hom.cohomologyFinrank p
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1 := sorry

/-- A reduced proper scheme of dimension at most one is unchanged by a proper
birational morphism with surjective global functions and equal first
structure-sheaf cohomology finranks. -/
theorem isIso_of_structureSheafH1Finrank_eq
    {k : Type u} [Field k] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X' ⟶ X) [IsBirational f] [IsProper f] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hΓ : Function.Surjective f.appTop)
    (hH1 : Scheme.Hom.cohomologyFinrank (f ≫ p)
        (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) 1 =
      Scheme.Hom.cohomologyFinrank p
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1) :
    IsIso f := sorry

end Scheme.Hom.ProperBirational
end AlgebraicGeometry
