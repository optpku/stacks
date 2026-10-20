/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.FinitePart

/-! # Scheme and separated finite-part localizations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.instFlat_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) [AlgebraicGeometry.Flat h.left],
    AlgebraicSpace.Flat (ofOverMap h))

#check (AlgebraicGeometry.AlgebraicSpace.instLocallyOfFinitePresentation_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.LocallyOfFinitePresentation h.left],
    AlgebraicSpace.LocallyOfFinitePresentation (ofOverMap h))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instIsScheme_withSectionSpace :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] [Flat f] [LocallyOfFinitePresentation f] [IsScheme Y]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y), IsScheme (FinitePart.withSectionSpace f σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.instSeparated_withSectionToY :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] [Flat f] [LocallyOfFinitePresentation f]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y), Separated (FinitePart.withSectionToY f σ hσ))
