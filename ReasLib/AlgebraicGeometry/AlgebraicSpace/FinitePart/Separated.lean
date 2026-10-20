/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.AlgebraicSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# The finite part of a separated flat locally finite-presentation morphism

The structure morphism of the finite part of a separated, flat, locally finitely
presented morphism is separated and representable. Its source is a scheme when
the target is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The structure morphism of the finite part of a separated, flat, locally
finitely presented morphism of algebraic spaces is separated. -/
instance instSeparated_spaceHom (f : X ⟶ Y) [Separated f] [Flat f]
    [LocallyOfFinitePresentation f] : Separated (spaceHom f) :=
  sorry

/-- The structure morphism of the finite part of a separated, flat, locally
finitely presented morphism of algebraic spaces is representable by schemes. -/
theorem relativelyRepresentable_spaceHom (f : X ⟶ Y) [Separated f] [Flat f]
    [LocallyOfFinitePresentation f] :
    yoneda.relativelyRepresentable (spaceHom f) :=
  sorry

/-- The finite part of a separated, flat, locally finitely presented morphism
of algebraic spaces is a scheme when its target is a scheme. -/
instance instIsScheme_space (f : X ⟶ Y) [Separated f] [Flat f]
    [LocallyOfFinitePresentation f] [IsScheme Y] : IsScheme (space f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
