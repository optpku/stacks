/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Representable quasi-compact morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is
quasi-compact in the scheme-slice sense of algebraic spaces if and only if
every 2-fibre product against a quasi-compact algebraic stack remains a
quasi-compact algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 101.7.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks which is
representable by algebraic spaces. Then `f` is quasi-compact as in Properties
of Stacks, Section 100.3 if and only if for every quasi-compact algebraic
stack `Z` and morphism `Z ⟶ Y` the algebraic stack `Z ×_Y X` is
quasi-compact. -/
@[stacks 050T]
theorem has_quasiCompact_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.QuasiCompact S) f ↔ AlgebraicStack.QuasiCompact f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that is
quasi-compact on scheme-slice tests of algebraic spaces is quasi-compact as a
morphism of algebraic stacks. -/
theorem quasiCompact_of_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : has (@AlgebraicSpace.QuasiCompact S) f) :
    AlgebraicStack.QuasiCompact f :=
  sorry

/-- A quasi-compact morphism of algebraic stacks that is representable by
algebraic spaces is quasi-compact on scheme-slice tests of algebraic spaces. -/
theorem has_of_quasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [AlgebraicStack.QuasiCompact f] :
    has (@AlgebraicSpace.QuasiCompact S) f :=
  sorry

/-- Quasi-compactness of a representable morphism of algebraic stacks in the
scheme-slice sense is equivalent to quasi-compactness of every chosen
2-fibre product `Z ×_Y X` against a quasi-compact algebraic stack. -/
theorem has_quasiCompact_iff_forall {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.QuasiCompact S) f ↔
      ∀ {Z : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack.IsQuasiCompact Z]
        (g : Z ⟶ Y)
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        AlgebraicStack.IsQuasiCompact
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
