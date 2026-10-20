module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Surjective
import StacksCheckRecall

/-!
# Quasi-compactness along a surjection of algebraic spaces

A surjective morphism of algebraic spaces sends a quasi-compact source to a
quasi-compact target. Equivalently, quasi-compactness of morphisms cancels
along a surjection in a commutative triangle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.8.6 (1): if `f : X ⟶ Y` is a surjective morphism of algebraic
spaces over `S` and `X` is quasi-compact, then `Y` is quasi-compact. -/
@[stacks 040W] #check (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact.of_surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [Surjective f] → [IsQuasiCompact X] → IsQuasiCompact Y)

/- Lemma 67.8.6 (2): if `f : X ⟶ Y` and `q : Y ⟶ Z` are morphisms of algebraic
spaces over `S`, `f` is surjective, and the composite `f ≫ q` is quasi-compact,
then `q` is quasi-compact. -/
@[stacks 040W] #check (AlgebraicGeometry.AlgebraicSpace.QuasiCompact.of_comp_surjective :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z),
    [Surjective f] → [QuasiCompact (f ≫ q)] → QuasiCompact q)

end AlgebraicGeometry.AlgebraicSpace
