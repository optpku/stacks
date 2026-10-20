module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom.Properties
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 106.4.1 (1): affine morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.affine_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      Groupoids.Hom.Affine f ↔ Groupoids.Hom.Affine f')

/- Lemma 106.4.1 (2): surjective morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.surjective_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.Surjective f ↔ AlgebraicStack.Surjective f')

/- Lemma 106.4.1 (3): quasi-compact morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.quasiCompact_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.QuasiCompact f ↔ AlgebraicStack.QuasiCompact f')

/- Lemma 106.4.1 (4): universally closed morphisms are invariant under a morphism
of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.universallyClosed_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.UniversallyClosed f ↔ AlgebraicStack.UniversallyClosed f')

/- Lemma 106.4.1 (5): integral morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.isIntegralHom_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.IsIntegralHom f ↔ AlgebraicStack.IsIntegralHom f')

/- Lemma 106.4.1 (6): universally injective morphisms are invariant under a
morphism of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.universallyInjective_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.UniversallyInjective f ↔ AlgebraicStack.UniversallyInjective f')

/- Lemma 106.4.1 (7): universally open morphisms are invariant under a morphism
of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.universallyOpen_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.UniversallyOpen f ↔ AlgebraicStack.UniversallyOpen f')

/- Lemma 106.4.1 (8): quasi-DM morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.quasiDM_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.QuasiDM f ↔ AlgebraicStack.QuasiDM f')

/- Lemma 106.4.1 (9): DM morphisms are invariant under a morphism of thickenings
of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.dm_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.DM f ↔ AlgebraicStack.DM f')

/- Lemma 106.4.1 (10): quasi-separated morphisms are invariant under a morphism
of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.quasiSeparated_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.QuasiSeparated f ↔ AlgebraicStack.QuasiSeparated f')

/- Lemma 106.4.1 (10): separated morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.separated_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      AlgebraicStack.Separated f ↔ AlgebraicStack.Separated f')

/- Lemma 106.4.1 (11): representable morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.relativelyRepresentable_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      FiberedCategoryOver.Groupoids.relativelyRepresentable f ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable f')

/- Lemma 106.4.1 (12): morphisms representable by algebraic spaces are invariant
under a morphism of thickenings of algebraic stacks. -/
@[stacks 0CJ9] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.Hom.relativelyRepresentableByAlgebraicSpaces_iff :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [AlgebraicStack.IsThickening i]
      [AlgebraicStack.IsThickening j] {f : X ⟶ Y} {f' : X' ⟶ Y'}
      (h : AlgebraicStack.IsThickening.Hom i j f f'),
      relativelyRepresentableByAlgebraicSpaces f ↔
      relativelyRepresentableByAlgebraicSpaces f')
