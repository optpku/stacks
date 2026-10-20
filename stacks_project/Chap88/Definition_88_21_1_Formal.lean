/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.FormalSpace.AdicDiagram

/-!
# Formal-space inputs to rig-surjectivity

The formal atlas, local Noetherian property and finite-type morphism APIs are owned by
ReasLib. Noetherian affine charts use the canonical quotient-power diagram; its comparison
with `AdicPresentation.diagram` respects all structure morphisms and transitions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace :
  ∀ {S : Scheme.{u}}, ((Over S)ᵒᵖ ⥤ Type u) → Prop)
#check (AlgebraicGeometry.FormalAlgebraicSpace.IsNoetherianAffine :
  ∀ {S : Scheme.{u}}, ((Over S)ᵒᵖ ⥤ Type u) → Prop)
#check (AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [FormalAlgebraicSpace.IsFormalAlgebraicSpace X],
    Prop)
#check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)
