module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothFiniteTypeObject.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.13.8: let `S` be a locally Noetherian scheme, let `X` be a category
fibred in groupoids over `(Sch/S)_fppf`, and let `k` be a finite type field over
`S` with an object `x0` of `X` over `Spec(k)` with image `s`. Assume the
diagonal `Δ : X ⟶ X × X` is representable by algebraic spaces, `X` satisfies
axioms [1], [2], [3], every formal object of `X` is effective, openness of
versality holds for `X`, and `𝒪_{S,s}` is a G-ring. Then there exist a finite
type morphism `U ⟶ S` and an object `x` of `X` over `U` such that the 2-Yoneda
1-morphism `(Sch/U)_fppf ⟶ X` is smooth, and a finite type point `u0` of `U`
with residue field `k` such that `x|_{u0} ≅ x0`. -/
@[stacks 07XY] #check (AlgebraicGeometry.GroupoidsOver.nonempty_smoothFiniteTypeObject :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X] [OpennessOfVersality X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObject X, FormalObject.IsEffective ξ)
    {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType kToS] (x0 : X.p.Fiber (Over.mk kToS)) (s : S)
    (hs : kToS (closedPoint k) = s) [IsGRing (S.presheaf.stalk s)],
    Nonempty (SmoothFiniteTypeObject kToS x0))

end AlgebraicGeometry.GroupoidsOver
