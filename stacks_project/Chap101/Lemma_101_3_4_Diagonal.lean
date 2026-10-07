module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Diagonals of representable morphisms of algebraic stacks

If a morphism of algebraic stacks is representable by algebraic spaces, then
its relative 2-diagonal is representable by schemes, a monomorphism, separated,
and locally quasi-finite in the scheme-slice sense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is representable by schemes. -/
theorem relativelyRepresentable_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    FiberedCategoryOver.Groupoids.relativelyRepresentable
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

namespace Mono

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is a monomorphism in the scheme-slice sense. -/
instance diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    let _ := hf
    Mono (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end Mono

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is separated on scheme-slice tests. -/
theorem has_separated_diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.Separated S) (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- The relative 2-diagonal of a morphism of algebraic stacks representable by
algebraic spaces is locally quasi-finite on scheme-slice tests. -/
theorem has_locallyQuasiFinite_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.LocallyQuasiFinite S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A representing algebraic space for the relative 2-diagonal of a morphism of
algebraic stacks representable by algebraic spaces is a scheme. -/
theorem isScheme_of_represents_diagonal {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) {U : Over S}
    {y : GroupoidsOver.slice U ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f f}
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange (Hom.diagonal.{u + 1, u, u + 1} f) y Fy fy) :
    AlgebraicSpace.IsScheme Fy :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
