/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen

/-!
# Relative diagonals of morphisms of thickenings

For a morphism of thickenings of algebraic stacks, each listed morphism
property holds for the relative diagonal of `f` if and only if it holds for
the relative diagonal of `f'`.
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

/-- The relative diagonals of a morphism of thickenings are simultaneously
representable by schemes. -/
theorem diagonal_relativelyRepresentable_iff (h : Hom i j f f') :
    FiberedCategoryOver.Groupoids.relativelyRepresentable
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
affine. -/
theorem diagonal_affine_iff (h : Hom i j f f') :
    Groupoids.Hom.Affine
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Affine
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
surjective. -/
theorem diagonal_surjective_iff (h : Hom i j f f') :
    AlgebraicStack.Surjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.Surjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
quasi-compact. -/
theorem diagonal_quasiCompact_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiCompact
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.QuasiCompact
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
universally closed. -/
theorem diagonal_universallyClosed_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyClosed
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyClosed
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
integral. -/
theorem diagonal_isIntegralHom_iff (h : Hom i j f f') :
    AlgebraicStack.IsIntegralHom
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.IsIntegralHom
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
quasi-separated in the scheme-slice sense. -/
theorem diagonal_quasiSeparated_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
separated in the scheme-slice sense. -/
theorem diagonal_separated_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
universally injective. -/
theorem diagonal_universallyInjective_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyInjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyInjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
universally open. -/
theorem diagonal_universallyOpen_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyOpen
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyOpen
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
locally quasi-finite in the scheme-slice sense. -/
theorem diagonal_locallyQuasiFinite_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
finite. -/
theorem diagonal_isFinite_iff (h : Hom i j f f') :
    AlgebraicStack.IsFinite
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.IsFinite
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
unramified in the scheme-slice sense. -/
theorem diagonal_unramified_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
monomorphisms. -/
theorem diagonal_mono_iff (h : Hom i j f f') :
    Groupoids.Hom.Mono
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Mono
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
immersions. -/
theorem diagonal_isImmersion_iff (h : Hom i j f f') :
    Groupoids.Hom.Immersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Immersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
closed immersions. -/
theorem diagonal_isClosedImmersion_iff (h : Hom i j f f') :
    Groupoids.Hom.ClosedImmersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.ClosedImmersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
proper in the scheme-slice sense. -/
theorem diagonal_proper_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Proper S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsThickening.Hom
