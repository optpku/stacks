module

public import Mathlib.Data.Set.Countable
public import stacks_project.Chap87.Lemma_87_14_6
public import stacks_project.Chap87.Lemma_87_14_7_Counterexample
public import stacks_project.Chap87.Lemma_87_38_5_Types

/-!
# Countably indexed affine completions along a countably cut-out closed subset

For an affine scheme `X = Spec(A)` over `S` and a closed subset `T ⊆ X`, if
the formal completion `X_/T` is countably indexed and `T` is cut out by
countably many functions in `A`, then `X_/T` is adic*. The countable-cut-out
hypothesis is necessary: Gabber's `ω₁`-algebra is a counterexample.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The affine meaning of a countably indexed formal completion along `T`:
there is a nested sequence of ideals `J n` with `V(J n) = T`, cofinal among
all ideals cutting out `T`. -/
def IsCountablyIndexedAlong {A : Type u} [CommRing A]
    (T : Closeds (Spec (.of A))) : Prop :=
  ∃ J : ℕ → Ideal A,
    Antitone J ∧
      (∀ n, T = zeroLocusCloseds (J n)) ∧
        ∀ I, T = zeroLocusCloseds I → ∃ n, J n ≤ I

/-- `IsCountablyIndexedAlong T` is the existence of a nested cofinal family of
ideals with zero locus `T`. -/
theorem isCountablyIndexedAlong_iff {A : Type u} [CommRing A]
    (T : Closeds (Spec (.of A))) :
    IsCountablyIndexedAlong T ↔
      ∃ J : ℕ → Ideal A,
        Antitone J ∧
          (∀ n, T = zeroLocusCloseds (J n)) ∧
            ∀ I, T = zeroLocusCloseds I → ∃ n, J n ≤ I :=
  sorry

/-- A closed subset `T ⊆ Spec(A)` is cut out by countably many functions in
`A`. Finite sets of functions are included, since they are countable. -/
def cutOutByCountable {A : Type u} [CommRing A]
    (T : Closeds (Spec (.of A))) : Prop :=
  ∃ s : Set A, s.Countable ∧ T = zeroLocusCloseds (Ideal.span s)

/-- `cutOutByCountable T` is equivalent to `T = V(f i)` for a countable family
of functions `f : ι → A`. -/
theorem cutOutByCountable_iff {A : Type u} [CommRing A]
    (T : Closeds (Spec (.of A))) :
    cutOutByCountable T ↔
      ∃ (ι : Type u) (_ : Countable ι) (f : ι → A),
        T = zeroLocusCloseds (Ideal.span (Set.range f)) :=
  sorry

/-- Lemma 87.14.7 (1): Let `S` be a scheme. Let `X = Spec(A)` be an affine
scheme over `S`. Let `T ⊂ X` be a closed subscheme. If the formal completion
`X_/T` is countably indexed and there exist countably many functions in `A`
such that `T = V(f₁, f₂, …)`, then `X_/T` is adic*. -/
@[stacks 0APW]
theorem isAdicStarAffine_of_countablyIndexedAlong {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) (hidx : IsCountablyIndexedAlong T)
    (hgen : cutOutByCountable T) :
    IsAdicStarAffine (affineCompletionAlong structureHom T) :=
  sorry

/-- Gabber's zero locus `V(x_α)` is countably indexed by the nested ideals
`J n = (x_α^(n+1))`. -/
theorem gabber_isCountablyIndexedAlong (k : Type u) [Field k] :
    IsCountablyIndexedAlong (counterexample.zeroLocus k) :=
  sorry

/-- Gabber's zero locus `V(x_α)` cannot be cut out by countably many
functions in the Gabber algebra. -/
theorem not_cutOutByCountable_gabber (k : Type u) [Field k] :
    ¬ cutOutByCountable (counterexample.zeroLocus k) :=
  sorry

/-- Lemma 87.14.7 (2): The conclusion of (1) is wrong if we omit the assumption
that `T` can be cut out by countably many functions. For a field `k`, Gabber's
`ω₁`-indexed `k`-algebra yields a countably indexed completion along
`V(x_α)` that is not adic*. -/
@[stacks 0APW]
theorem gabber_not_isAdicStarAffine (k : Type u) [Field k] :
    ¬ IsAdicStarAffine
        (affineCompletionAlong (counterexample.structureHom k)
          (counterexample.zeroLocus k)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
