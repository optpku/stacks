module

public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Cancellation of quasi-compactness along a surjection of algebraic stacks

If a morphism of algebraic stacks is surjective and a 2-isomorphic hypotenuse
(or the strict composite) is quasi-compact, then the second factor is
quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- Lemma 101.7.6: Let `f : X ⟶ Y`, `p : X ⟶ Z`, and `q : Y ⟶ Z` be a
2-commutative triangle of morphisms of algebraic stacks. If `f` is surjective
and `p` is quasi-compact, then `q` is quasi-compact. The reusable form
identifies the hypotenuse `p` with the composite `f ≫ q` up to a
2-isomorphism. -/
@[stacks 050X]
theorem of_comp_surjective {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (q : Y ⟶ Z) [Surjective f] [QuasiCompact (f ≫ q)] :
    QuasiCompact q :=
  sorry

/-- Quasi-compactness of `q : Y ⟶ Z` follows from surjectivity of `f : X ⟶ Y`
and quasi-compactness of a 2-isomorphic hypotenuse `p ≅ f ≫ q`. -/
theorem of_two_commute {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (α : p ≅ f ≫ q)
    [Surjective f] [QuasiCompact p] : QuasiCompact q :=
  sorry

/-- Quasi-compactness of morphisms of algebraic stacks is invariant under
2-isomorphism. -/
theorem iso_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f g : X ⟶ Y} (α : f ≅ g) :
    QuasiCompact f ↔ QuasiCompact g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
