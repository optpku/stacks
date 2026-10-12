/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.relativeAssassin

/-- If a flat morphism of schemes over `S` covers the relative associated points of a
finite-type quasicoherent module that is flat over `S`, then its pullback-pushforward unit is a
monomorphism. -/
theorem unit_mono_of_subset_range {S : Scheme.{u}} (X X' : Over S) (g : X' ⟶ X)
    [Flat g.left] [LocallyOfFiniteType X.hom] (F : X.left.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType]
    [SheafOfModules.IsFlatOver F X.hom.toShHom]
    (h_ass : relativeAssassin X.hom F ⊆ Set.range g.left) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app F) := sorry

/-- Under the relative associated-point coverage criterion, the pullback-pushforward unit remains
a monomorphism after an arbitrary base change. -/
theorem unit_mono_afterBaseChange_of_subset_range {S : Scheme.{u}}
    (X X' : Over S) (g : X' ⟶ X) [Flat g.left] [LocallyOfFiniteType X.hom]
    (F : X.left.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [SheafOfModules.IsFlatOver F X.hom.toShHom]
    (h_ass : relativeAssassin X.hom F ⊆ Set.range g.left)
    {T : Scheme.{u}} (s : T ⟶ S) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction ((Over.pullback s).map g).left).unit.app
      (Scheme.Modules.baseChangeModule X.hom s F)) := sorry

end Scheme.Modules.relativeAssassin
end AlgebraicGeometry
