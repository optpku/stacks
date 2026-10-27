/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Set.Countable
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineCompletion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation

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
  Iff.rfl

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

/-- The completion of an affine scheme along a closed subset is countably
indexed if and only if the ideals with that zero locus admit a nested
countable cofinal family. -/
theorem isCountablyIndexedAffine_completionAlong_iff {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A))) :
    IsCountablyIndexedAffine (affineCompletionAlong structureHom T) ↔
      IsCountablyIndexedAlong T :=
  sorry

/-- A countably indexed affine completion along a closed subset cut out by
countably many functions is adic*, with a finitely generated ideal of
definition. -/
theorem isAdicStarAffine_of_countablyIndexedAlong {S : Scheme.{u}}
    {A : Type u} [CommRing A] (structureHom : Spec (.of A) ⟶ S)
    (T : Closeds (Spec (.of A)))
    [IsCountablyIndexedAffine (affineCompletionAlong structureHom T)]
    (hgen : cutOutByCountable T) :
    IsAdicStarAffine (affineCompletionAlong structureHom T) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
