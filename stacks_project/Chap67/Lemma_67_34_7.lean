/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_34_7_QuasiFiniteLocus

/-!
# Quasi-finite part of a locally finite-type morphism of algebraic spaces

A locally finite-type morphism of algebraic spaces has a canonical open
subspace of the source on which it is locally quasi-finite, the relative
dimension is at least `1` off that open, and formation of the open commutes
with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.34.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. The restriction
of `f` along the canonical open subspace `quasiFiniteLocus f` is locally
quasi-finite, and the relative dimension of `f` at any point of `Points X`
outside `Set.range (Points.map (quasiFiniteLocus f).ι)` is at least `1`. -/
@[stacks 04NW]
theorem locallyQuasiFinite_quasiFiniteLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) ∧
      ∀ x : Points X, x ∉ Set.range (Points.map (quasiFiniteLocus f).ι) →
        (1 : WithBot ℕ∞) ≤ fiberDimensionAt f x :=
  sorry

/-- Lemma 67.34.7 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. Formation of
the canonical open subspace `quasiFiniteLocus f` commutes with arbitrary base
change. -/
@[stacks 04NW]
theorem quasiFiniteLocus_pointsSet_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] :
    Set.range (Points.map (quasiFiniteLocus f').ι) =
      Points.map g' ⁻¹' Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
