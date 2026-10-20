/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Smoothness versus formal smoothness of algebraic spaces

A morphism of algebraic spaces over a scheme is smooth exactly when it is
locally of finite presentation and formally smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is smooth if and only if it is locally of
finite presentation and formally smooth. -/
theorem Smooth.iff_locallyOfFinitePresentation_and_formallySmooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Smooth f ↔ LocallyOfFinitePresentation f ∧ FormallySmooth f :=
  sorry

/-- A smooth morphism of algebraic spaces is formally smooth. -/
instance FormallySmooth.of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] : FormallySmooth f :=
  (Smooth.iff_locallyOfFinitePresentation_and_formallySmooth f).mp ‹Smooth f› |>.2

/-- A locally finitely presented, formally smooth morphism of algebraic spaces is
smooth. -/
instance Smooth.of_locallyOfFinitePresentation_of_formallySmooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [FormallySmooth f] : Smooth f :=
  (Smooth.iff_locallyOfFinitePresentation_and_formallySmooth f).mpr
    ⟨‹LocallyOfFinitePresentation f›, ‹FormallySmooth f›⟩

end AlgebraicGeometry.AlgebraicSpace
