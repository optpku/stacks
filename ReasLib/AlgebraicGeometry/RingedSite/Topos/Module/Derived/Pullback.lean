/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived module pullback along a morphism of ringed topoi

This file derives the presentation-independent module pullback attached to
`RingedSite.ToposHom`.  The morphism of topoi and its inverse-image structure map remain the
only geometric data exposed to downstream users.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- The homotopy-to-derived functor induced by module pullback along an arbitrary morphism of
site-presented ringed topoi. -/
@[stacks 06YY "ringed-topos pullback to the derived category"]
abbrev modulePullbackToDerived (f : ToposHom X Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] :
    RingedSite.Hom.ModuleHomotopy.{w} Y ⥤ RingedSite.Hom.ModuleDerived.{w} X :=
  f.modulePullbackHomotopy ⋙ RingedSite.Hom.moduleLocalization X

/-- Existence of the unbounded total left derived module pullback along a morphism of ringed
topoi. -/
@[stacks 06YY "existence of ringed-topos derived pullback"]
abbrev HasModulePullbackDerived (f : ToposHom X Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint] : Prop :=
  Functor.HasLeftDerivedFunctor (modulePullbackToDerived f)
    (RingedSite.Hom.ModuleQis.{w} Y)

/-- The canonical unbounded total left derived inverse image on modules along an arbitrary
morphism of site-presented ringed topoi. -/
@[stacks 06YY "ringed-topos derived module pullback"]
noncomputable abbrev modulePullbackDerived (f : ToposHom X Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [HasModulePullbackDerived f] :
    RingedSite.Hom.ModuleDerived.{w} Y ⥤ RingedSite.Hom.ModuleDerived.{w} X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (RingedSite.Hom.moduleLocalization Y) (RingedSite.Hom.ModuleQis Y)

end RingedSite.ToposHom
