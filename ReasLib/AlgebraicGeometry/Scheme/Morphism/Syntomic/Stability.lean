/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Stability of syntomic scheme morphisms

The syntomic morphism property is stable under identities, composition, and
base change.  This leaf packages those facts in the standard
`MorphismProperty` typeclasses used by covers and sites.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- A syntomic morphism remains syntomic after composition with a syntomic
morphism. -/
@[stacks 01UH]
theorem syntomic_comp (hf : Syntomic f) (hg : Syntomic g) :
    Syntomic (f ≫ g) := sorry

/-- The syntomic property is stable under composition. -/
theorem syntomic_isStableUnderComposition :
    CategoryTheory.MorphismProperty.IsStableUnderComposition @Syntomic := sorry

/-- Instance form of stability of syntomic morphisms under composition. -/
instance instSyntomicIsStableUnderComposition :
    CategoryTheory.MorphismProperty.IsStableUnderComposition @Syntomic := sorry

/-- Identities of schemes are syntomic. -/
theorem syntomic_id (X : Scheme.{u}) : Syntomic (𝟙 X) := sorry

/-- The syntomic property contains identities. -/
instance instSyntomicContainsIdentities :
    CategoryTheory.MorphismProperty.ContainsIdentities @Syntomic := sorry

/-- The pullback of a syntomic morphism is syntomic. -/
@[stacks 01UI]
theorem syntomic_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (hf : Syntomic f) (g : S' ⟶ S) :
    Syntomic (pullback.snd f g) := sorry

/-- The syntomic property is stable under arbitrary base change. -/
instance instSyntomicIsStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange @Syntomic := sorry

/-- Syntomic morphisms form a multiplicative morphism property. -/
instance instSyntomicIsMultiplicative :
    CategoryTheory.MorphismProperty.IsMultiplicative @Syntomic := sorry

end AlgebraicGeometry
