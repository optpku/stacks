module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.Surjective
import StacksCheckRecall

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

/- Lemma 101.7.6: Let `f : X ⟶ Y`, `p : X ⟶ Z`, and `q : Y ⟶ Z` be a
2-commutative triangle of morphisms of algebraic stacks. If `f` is surjective
and `p` is quasi-compact, then `q` is quasi-compact. The reusable form
identifies the hypotenuse `p` with the composite `f ≫ q` up to a
2-isomorphism. -/
@[stacks 050X] #check (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_two_commute :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (α : p ≅ f ≫ q)
    [Surjective f] [QuasiCompact p], QuasiCompact q)

#check (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_comp_surjective :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (q : Y ⟶ Z) [Surjective f] [QuasiCompact (f ≫ q)],
    QuasiCompact q)

#check (AlgebraicGeometry.AlgebraicStack.QuasiCompact.iso_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f g : X ⟶ Y} (α : f ≅ g),
    QuasiCompact f ↔ QuasiCompact g)

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
