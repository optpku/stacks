module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
import StacksCheckRecall

/-!
# Trivial implications among separation axioms

A separated morphism of algebraic stacks is quasi-separated, a DM morphism is
quasi-DM, and a morphism representable by algebraic spaces is DM.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.4.3 (1): A separated morphism of algebraic stacks is
quasi-separated. -/
@[stacks 050E] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.of_separated :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicStack.Separated f],
      AlgebraicGeometry.AlgebraicStack.QuasiSeparated f)

/- Lemma 101.4.3 (2): A DM morphism of algebraic stacks is quasi-DM. -/
@[stacks 050E] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiDM.of_DM :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicStack.DM f],
      AlgebraicGeometry.AlgebraicStack.QuasiDM f)

/- Lemma 101.4.3 (3): A morphism of algebraic stacks representable by
algebraic spaces is DM. -/
@[stacks 050E] #check
  (AlgebraicGeometry.AlgebraicStack.DM.of_relativelyRepresentableByAlgebraicSpaces :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f → AlgebraicGeometry.AlgebraicStack.DM f)
