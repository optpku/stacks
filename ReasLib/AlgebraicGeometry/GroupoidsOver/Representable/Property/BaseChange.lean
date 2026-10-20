/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Base change of representable morphisms having a morphism property

Properties of algebraic-space morphisms stable under base change and fppf local
on the target are inherited by base changes of representable 1-morphisms of
groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- If a property of algebraic-space morphisms is stable under base change and
fppf local on the target, the first projection of a two-fibre product has that
property whenever the morphism being base changed is representable by algebraic
spaces and has that property. -/
theorem has.pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (g : Z ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hP : has P f) :
    has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) := sorry

end AlgebraicGeometry.Groupoids.Hom
