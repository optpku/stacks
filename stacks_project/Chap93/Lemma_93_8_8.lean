module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization
import StacksCheckRecall

/-!
# Henselization of ring deformations
-/

@[expose] public section

open CategoryTheory FlatAlgebraCat

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P] (J : Ideal P)

/- Lemma 93.8.8: in Example 93.8.1, if `P` is a `k`-algebra and `J ⊂ P` is an
ideal, with `(P^h, J^h)` the henselization of the pair `(P, J)` given by
`henselizationRing (pairOfIdeal J)` and `henselizationIdeal (pairOfIdeal J)`,
there is a natural functor `Def_P ⟶ Def_{P^h}` of deformation categories,
sending a deformation `(A, Q) ⟶ (k, P)` to `(A, Q^h) ⟶ (k, P^h)`. -/
@[stacks 0DYT]
#check (FlatAlgebraCat.henselizationFunctor Λ k P J :
  FlatAlgebraCat.deformationCategory Λ k P ⥤
    FlatAlgebraCat.deformationCategory Λ k
      (RingPairCat.henselizationRing (RingPairCat.pairOfIdeal J) : Type u))

end
