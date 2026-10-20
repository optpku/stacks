/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen

/-!
# Morphism properties invariant under morphisms of thickenings of stacks

For a morphism of thickenings of algebraic stacks, each listed morphism
property holds for `f` if and only if it holds for `f'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening.Hom

variable {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
variable {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- Affine morphisms are invariant under a morphism of thickenings of algebraic
stacks. -/
theorem affine_iff (h : Hom i j f f') :
    Groupoids.Hom.Affine f ↔ Groupoids.Hom.Affine f' :=
  sorry

/-- Surjective morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem surjective_iff (h : Hom i j f f') :
    AlgebraicStack.Surjective f ↔ AlgebraicStack.Surjective f' :=
  sorry

/-- Quasi-compact morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem quasiCompact_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiCompact f ↔ AlgebraicStack.QuasiCompact f' :=
  sorry

/-- Universally closed morphisms are invariant under a morphism of thickenings
of algebraic stacks. -/
theorem universallyClosed_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyClosed f ↔ AlgebraicStack.UniversallyClosed f' :=
  sorry

/-- Integral morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem isIntegralHom_iff (h : Hom i j f f') :
    AlgebraicStack.IsIntegralHom f ↔ AlgebraicStack.IsIntegralHom f' :=
  sorry

/-- Universally injective morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
theorem universallyInjective_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyInjective f ↔ AlgebraicStack.UniversallyInjective f' :=
  sorry

/-- Universally open morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem universallyOpen_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyOpen f ↔ AlgebraicStack.UniversallyOpen f' :=
  sorry

/-- Quasi-DM morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem quasiDM_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiDM f ↔ AlgebraicStack.QuasiDM f' :=
  sorry

/-- DM morphisms are invariant under a morphism of thickenings of algebraic
stacks. -/
theorem dm_iff (h : Hom i j f f') :
    AlgebraicStack.DM f ↔ AlgebraicStack.DM f' :=
  sorry

/-- Quasi-separated morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem quasiSeparated_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiSeparated f ↔ AlgebraicStack.QuasiSeparated f' :=
  sorry

/-- Separated morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem separated_iff (h : Hom i j f f') :
    AlgebraicStack.Separated f ↔ AlgebraicStack.Separated f' :=
  sorry

/-- Representable morphisms, in the scheme-valued sense, are invariant under a
morphism of thickenings of algebraic stacks. -/
theorem relativelyRepresentable_iff (h : Hom i j f f') :
    FiberedCategoryOver.Groupoids.relativelyRepresentable f ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable f' :=
  sorry

/-- Morphisms representable by algebraic spaces are invariant under a morphism
of thickenings of algebraic stacks. -/
theorem relativelyRepresentableByAlgebraicSpaces_iff (h : Hom i j f f') :
    relativelyRepresentableByAlgebraicSpaces f ↔
      relativelyRepresentableByAlgebraicSpaces f' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening.Hom
