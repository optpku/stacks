/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_4_1_Separation

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

namespace DM

/-- Lemma 101.4.10 (1): The composition of a pair of DM morphisms of algebraic
stacks is DM.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 050K]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [DM f] [DM g] :
    DM (f ≫ g) :=
  sorry

end DM

namespace QuasiDM

/-- Lemma 101.4.10 (2): The composition of a pair of quasi-DM morphisms of
algebraic stacks is quasi-DM.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 050K]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiDM f] [QuasiDM g] :
    QuasiDM (f ≫ g) :=
  sorry

end QuasiDM

namespace Separated

/-- Lemma 101.4.10 (3): The composition of a pair of separated morphisms of
algebraic stacks is separated.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 050K]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Separated f] [Separated g] :
    Separated (f ≫ g) :=
  sorry

end Separated

namespace QuasiSeparated

/-- Lemma 101.4.10 (4): The composition of a pair of quasi-separated morphisms
of algebraic stacks is quasi-separated.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 050K]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicStack
