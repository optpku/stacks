module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Finite separable extensions suffice for the existence part of the valuative criterion

For a morphism of algebraic spaces, the existence part of the valuative
criterion is equivalent to the same criterion restricted to dominating
extensions whose fraction-field extension is finite separable.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace ValuativeCriterion.Existence

/-- Lemma 67.41.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` satisfies the existence part of the
valuative criterion as in Definition 67.41.1 if and only if `f` satisfies the
existence part of the valuative criterion as in Definition 67.41.1 modified by
requiring the extension `K'/K` to be finite separable. -/
@[stacks 03KH]
theorem iff_exists_finiteSeparable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Existence f ↔ ∀ sq : ValuativeCommSq f,
      ∃ e : sq.Extension, FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' :=
  sorry

/-- If every valuative square admits a dominating extension with finite
separable fraction-field extension, then `f` satisfies the existence part of
the valuative criterion. -/
theorem of_exists_finiteSeparable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ sq : ValuativeCommSq f,
      ∃ e : sq.Extension, FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K') :
    Existence f :=
  sorry

/-- If `f` satisfies the existence part of the valuative criterion, then every
valuative square admits a dominating extension whose fraction-field extension
is finite separable. -/
theorem exists_finiteSeparable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Existence f] (sq : ValuativeCommSq f) :
    ∃ e : sq.Extension, FiniteDimensional sq.K e.K' ∧ Algebra.IsSeparable sq.K e.K' :=
  sorry

end ValuativeCriterion.Existence
end AlgebraicGeometry.AlgebraicSpace
