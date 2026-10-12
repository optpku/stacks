/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of projective scheme morphisms

This file collects base-change APIs for projective, H-projective, and locally projective
morphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Projective morphisms are stable under arbitrary base change. -/
instance projective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @Projective := sorry

/-- H-projective morphisms are stable under arbitrary base change. -/
instance hProjective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @HProjective := sorry

/-- Locally projective morphisms are stable under arbitrary base change. -/
instance locallyProjective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyProjective := sorry

/-- A base change of a projective morphism is projective. -/
theorem Projective.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : Projective f) (g : S' ⟶ S) :
    Projective (pullback.snd f g) := sorry

/-- A base-changed projective morphism has a projective structure. -/
instance instProjectivePullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [Projective f] :
    Projective (pullback.snd f g) := sorry

/-- The pullback projection of an H-projective morphism is H-projective. -/
@[stacks 01WF]
theorem HProjective.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : HProjective f) (g : S' ⟶ S) :
    HProjective (pullback.snd f g) := sorry

/-- A base-changed H-projective morphism has an H-projective structure. -/
instance instHProjectivePullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [HProjective f] :
    HProjective (pullback.snd f g) := sorry

/-- A base change of a locally projective morphism is locally projective. -/
theorem LocallyProjective.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : LocallyProjective f) (g : S' ⟶ S) :
    LocallyProjective (pullback.snd f g) := sorry

/-- A base-changed locally projective morphism has a locally projective structure. -/
instance instLocallyProjectivePullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyProjective f] :
    LocallyProjective (pullback.snd f g) := sorry

end AlgebraicGeometry
