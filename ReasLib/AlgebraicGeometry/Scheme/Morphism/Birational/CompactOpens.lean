/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints

/-!
# Birationality on quasi-compact opens

This file records the condition that a scheme morphism restricts to a birational morphism over
every quasi-compact open, with finite irreducible components in each inverse image.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism is birational on quasi-compact opens if the inverse image of every
quasi-compact open has finitely many irreducible components and the restricted morphism is
birational. -/
@[stacks 035Q "birationality on quasi-compact opens"]
def IsBirationalOnCompactOpens {X' X : Scheme.{u}} (α : X' ⟶ X) : Prop :=
  ∀ (U : X.Opens), IsCompact (U : Set X) →
    (irreducibleComponents (α ⁻¹ᵁ U)).Finite ∧ IsBirational (α ∣_ U)

/-- Birationality on quasi-compact opens unfolds into inverse-image component finiteness and
birationality of every restricted morphism. -/
@[stacks 035Q "birational-on-compact-opens criterion"]
theorem isBirationalOnCompactOpens_iff {X' X : Scheme.{u}} (α : X' ⟶ X) :
    α.IsBirationalOnCompactOpens ↔
      ∀ (U : X.Opens), IsCompact (U : Set X) →
        (irreducibleComponents (α ⁻¹ᵁ U)).Finite ∧ IsBirational (α ∣_ U) := sorry

end AlgebraicGeometry.Scheme.Hom
