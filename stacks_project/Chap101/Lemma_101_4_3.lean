module

public import stacks_project.Chap101.Definition_101_4_1_Separation

/-!
# Trivial implications among separation axioms

A separated morphism of algebraic stacks is quasi-separated, a DM morphism is
quasi-DM, and a morphism representable by algebraic spaces is DM.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace QuasiSeparated

/-- Lemma 101.4.3 (1): A separated morphism of algebraic stacks is
quasi-separated. -/
@[stacks 050E]
instance of_separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f] :
    QuasiSeparated f :=
  sorry

end QuasiSeparated

namespace QuasiDM

/-- Lemma 101.4.3 (2): A DM morphism of algebraic stacks is quasi-DM. -/
@[stacks 050E]
instance of_DM {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f] :
    QuasiDM f :=
  sorry

end QuasiDM

namespace DM

/-- Lemma 101.4.3 (3): A morphism of algebraic stacks representable by
algebraic spaces is DM. -/
@[stacks 050E]
instance of_relativelyRepresentableByAlgebraicSpaces
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    let _ := hf
    DM f :=
  sorry

end DM

end AlgebraicGeometry.AlgebraicStack
