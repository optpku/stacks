/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsPureAlong

/-- For a finitely presented morphism and a finitely presented module flat over the base,
the locus where the module is pure along the fibre is open. -/
theorem isOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (F : X.Modules)
    [F.IsFinitePresentation] [SheafOfModules.IsFlatOver F f.toShHom] :
    IsOpen {s : S | F.IsPureAlong f s} := sorry

end AlgebraicGeometry.Scheme.Modules.IsPureAlong
