module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_9_1_Affine
public import stacks_project.Chap101.Definition_101_10_1_Integral
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_14_2_UniversallyInjective
public import stacks_project.Chap101.Lemma_101_11_3_UniversallyOpen
public import stacks_project.Chap106.Lemma_106_3_7_Diagonal

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
