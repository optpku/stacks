module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.DiagonalProperties
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.IsThickening
open AlgebraicGeometry.AlgebraicStack.IsThickening.Hom
open scoped Bicategory

universe u

/- Lemma 106.3.8 (1): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously representable by schemes. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_relativelyRepresentable_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    FiberedCategoryOver.Groupoids.relativelyRepresentable
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (2): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously affine. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_affine_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.Affine
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Affine
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (3): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously surjective. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_surjective_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    AlgebraicStack.Surjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.Surjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (4): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously quasi-compact. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_quasiCompact_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    AlgebraicStack.QuasiCompact
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.QuasiCompact
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (5): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously universally closed. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_universallyClosed_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    AlgebraicStack.UniversallyClosed
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyClosed
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (6): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously integral. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_isIntegralHom_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    AlgebraicStack.IsIntegralHom
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.IsIntegralHom
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (7): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously quasi-separated. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_quasiSeparated_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (8): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously separated. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_separated_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (9): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously universally injective. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_universallyInjective_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    AlgebraicStack.UniversallyInjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyInjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (10): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously universally open. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_universallyOpen_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    AlgebraicStack.UniversallyOpen
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyOpen
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (11): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously locally quasi-finite. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_locallyQuasiFinite_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (12): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously finite. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_isFinite_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    AlgebraicStack.IsFinite
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.IsFinite
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (13): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously unramified. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_unramified_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (14): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously monomorphisms. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_mono_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.Mono
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Mono
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (15): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously immersions. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_isImmersion_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.Immersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Immersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (16): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously closed immersions. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_isClosedImmersion_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.ClosedImmersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.ClosedImmersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))

/- Lemma 106.3.8 (17): the relative diagonals of a morphism of thickenings of
algebraic stacks are simultaneously proper. -/
@[stacks 0BPV] #check
  (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.diagonal_proper_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (_ : Hom i j f f'),
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Proper S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f'))
