/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Separated

/-!
# Scheme representability and separatedness of finite parts containing a section

For a separated, flat, locally finitely presented morphism, the finite part
containing a section is separated over the target and is a scheme when the target is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The finite-part-with-section space `(X / Y, σ)_fin` is a scheme when `f` is
separated, flat, and locally of finite presentation and `Y` is a scheme. -/
instance instIsScheme_withSectionSpace (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] [Flat f] [LocallyOfFinitePresentation f] [IsScheme Y]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) : IsScheme (withSectionSpace f σ hσ) :=
  sorry

/-- The structure morphism `(X / Y, σ)_fin ⟶ Y` is separated when `f` is
separated, flat, and locally of finite presentation. -/
instance instSeparated_withSectionToY (f : X ⟶ Y) [Separated f]
    [LocallyOfFiniteType f] [Flat f] [LocallyOfFinitePresentation f]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) : Separated (withSectionToY f σ hσ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
