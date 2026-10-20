/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CartesianSystem

/-!
# Cartesian spaces-étale systems

Compatibility checks for cartesian systems and canonical pullback from the
spaces-étale site.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.CartesianSpacesEtaleSystem :
  {J : Type v} → [Category.{v} J] → {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (J ⥤ Over B) → Type (max (u + 1) v))

#check (AlgebraicGeometry.AlgebraicSpace.ofSpacesEtalePullback :
  ∀ {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
    {D : J ⥤ Over B} (c : Cocone D),
    spacesEtaleSite c.pt.left → CartesianSpacesEtaleSystem D)

#check (AlgebraicGeometry.AlgebraicSpace.IsInSpacesEtaleEssImage :
  ∀ {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
    {D : J ⥤ Over B} (c : Cocone D), CartesianSpacesEtaleSystem D → Prop)
