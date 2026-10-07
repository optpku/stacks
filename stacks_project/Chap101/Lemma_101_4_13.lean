module

public import stacks_project.Chap101.Lemma_101_4_13_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 101.4.13 (1): an algebraic stack over `S` is DM if and only if it is
DM over `S`. -/
@[stacks 050N] #check
  (IsDM.iff_over :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
      [AlgebraicStack X],
      IsDM X ↔ IsDMOver X)

/- Lemma 101.4.13 (2): an algebraic stack over `S` is quasi-DM if and only if
it is quasi-DM over `S`. -/
@[stacks 050N] #check
  (IsQuasiDM.iff_over :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
      [AlgebraicStack X],
      IsQuasiDM X ↔ IsQuasiDMOver X)

/- Lemma 101.4.13 (3): if an algebraic stack over `S` is separated, then it is
separated over `S`. -/
@[stacks 050N] #check
  (IsSeparatedOver.of_isSeparated :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
      [AlgebraicStack X] [IsSeparated X],
      IsSeparatedOver X)

/- Lemma 101.4.13 (4): if an algebraic stack over `S` is quasi-separated, then
it is quasi-separated over `S`. -/
@[stacks 050N] #check
  (IsQuasiSeparatedOver.of_isQuasiSeparated :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
      [AlgebraicStack X] [IsQuasiSeparated X],
      IsQuasiSeparatedOver X)

/- Lemma 101.4.13 (5): if `X` is DM over `S`, then a morphism `f : X ⟶ Y` of
algebraic stacks over `S` is DM. -/
@[stacks 050N] #check
  (DM.of_isDMOver :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y)
      [IsDMOver X],
      DM f)

/- Lemma 101.4.13 (6): if `X` is quasi-DM over `S`, then a morphism
`f : X ⟶ Y` of algebraic stacks over `S` is quasi-DM. -/
@[stacks 050N] #check
  (QuasiDM.of_isQuasiDMOver :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y)
      [IsQuasiDMOver X],
      QuasiDM f)

/- Lemma 101.4.13 (7): if `X` is separated over `S` and `diagonal Y` is
separated, then a morphism `f : X ⟶ Y` of algebraic stacks over `S` is
separated. -/
@[stacks 050N] #check
  (Separated.of_isSeparatedOver :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y)
      [IsSeparatedOver X],
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
          (diagonal.{u + 1, u, u + 1} Y) →
        Separated f)

/- Lemma 101.4.13 (8): if `X` is quasi-separated over `S` and `diagonal Y` is
quasi-separated, then a morphism `f : X ⟶ Y` of algebraic stacks over `S` is
quasi-separated. -/
@[stacks 050N] #check
  (QuasiSeparated.of_isQuasiSeparatedOver :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y)
      [IsQuasiSeparatedOver X],
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (diagonal.{u + 1, u, u + 1} Y) →
        QuasiSeparated f)
