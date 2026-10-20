/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Composition of transferred morphism properties of algebraic spaces

The transfer of a morphism property of algebraic spaces to presheaf morphisms
is stable under composition when the property is stable under base change,
fppf local on the target, and stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `a : F ⟶ G` and `b : G ⟶ H` satisfy `relativeAlgebraicSpaces P`, where
`P` is stable under base change, fppf local on the target, and stable under
composition, then so does `a ≫ b`. -/
theorem relativeAlgebraicSpaces.comp {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (fppfPrecoverage S)] [P.IsStableUnderComposition]
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    (ha : relativeAlgebraicSpaces P a) (hb : relativeAlgebraicSpaces P b) :
    relativeAlgebraicSpaces P (a ≫ b) := sorry

/-- The transfer of a morphism property of algebraic spaces that is stable under
base change, fppf local on the target, and stable under composition is stable
under composition of presheaf morphisms. -/
instance relativeAlgebraicSpaces.isStableUnderComposition {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (fppfPrecoverage S)] [P.IsStableUnderComposition] :
    (relativeAlgebraicSpaces P).IsStableUnderComposition where
  comp_mem a b ha hb := relativeAlgebraicSpaces.comp a b ha hb

end AlgebraicGeometry.AlgebraicSpace
