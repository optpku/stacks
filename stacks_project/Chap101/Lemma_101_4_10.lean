module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Composition
import StacksCheckRecall

/-!
# Composition of separation axioms for morphisms of algebraic stacks

Each of the separation axioms of Definition 101.4.1 is stable under
composition of morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.4.10 (1): The composition of DM morphisms of algebraic stacks is DM. -/
@[stacks 050K] #check (AlgebraicGeometry.AlgebraicStack.DM.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [DM f] [DM g],
    DM (f ≫ g))

/- Lemma 101.4.10 (2): The composition of quasi-DM morphisms of algebraic stacks
is quasi-DM. -/
@[stacks 050K] #check (AlgebraicGeometry.AlgebraicStack.QuasiDM.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiDM f] [QuasiDM g],
    QuasiDM (f ≫ g))

/- Lemma 101.4.10 (3): The composition of separated morphisms of algebraic stacks
is separated. -/
@[stacks 050K] #check (AlgebraicGeometry.AlgebraicStack.Separated.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g],
    Separated (f ≫ g))

/- Lemma 101.4.10 (4): The composition of quasi-separated morphisms of algebraic
stacks is quasi-separated. -/
@[stacks 050K] #check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g],
    QuasiSeparated (f ≫ g))

end AlgebraicGeometry.AlgebraicStack
