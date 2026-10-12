/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective

/-!
# Base change of quasi-projective scheme morphisms

Quasi-projective morphisms are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Quasi-projective morphisms are stable under arbitrary base change. -/
instance quasiProjective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiProjective := sorry

/-- The pullback projection obtained by base changing a quasi-projective morphism is
quasi-projective. -/
theorem QuasiProjective.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : QuasiProjective f) (g : S' ⟶ S) :
    QuasiProjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/-- A base-changed quasi-projective morphism has a quasi-projective structure. -/
instance instQuasiProjectivePullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiProjective f] :
    QuasiProjective (pullback.snd f g) :=
  QuasiProjective.pullback_snd inferInstance g

end AlgebraicGeometry
