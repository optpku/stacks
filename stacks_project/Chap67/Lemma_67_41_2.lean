module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Representable morphisms and the existence part of the valuative criterion

For a representable morphism of algebraic spaces, the existence part of the
valuative criterion is equivalent to the scheme-style existence of a dotted
arrow in every valuative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace ValuativeCriterion.Existence

/-- Lemma 67.41.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is representable. Then `f` satisfies the
existence part of the valuative criterion as in Definition 67.41.1 if and only
if, given any commutative solid diagram `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` where
`A` is a valuation ring with field of fractions `K`, there exists a dotted
arrow `Spec(A) ⟶ X`, i.e., `f` satisfies the existence part of the valuative
criterion as in Schemes, Definition 26.20.3
(`AlgebraicGeometry.ValuativeCriterion.Existence`). -/
@[stacks 03K8]
theorem iff_hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    Existence f ↔ ∀ sq : ValuativeCommSq f, sq.commSq.HasLift :=
  sorry

/-- The scheme-style existence of a dotted arrow in every valuative square
implies the existence part of the valuative criterion for morphisms of
algebraic spaces. -/
theorem of_hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ sq : ValuativeCommSq f, sq.commSq.HasLift) : Existence f :=
  sorry

/-- If a representable morphism of algebraic spaces satisfies the existence
part of the valuative criterion, then every valuative square admits a dotted
arrow. -/
theorem hasLift {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) [Existence f]
    (sq : ValuativeCommSq f) : sq.commSq.HasLift :=
  sorry

end ValuativeCriterion.Existence
end AlgebraicGeometry.AlgebraicSpace
