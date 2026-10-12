/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree

/-!
# Fibre-degree bounds at field-valued points

This file relates uniform fibre-degree bounds to pullbacks along field-valued
points and records their pointwise residue degrees.
-/

@[expose] public section

open CategoryTheory Limits
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The canonical scalar action of the source field on the residue field of a point of a
field-valued pullback. -/
noncomputable instance fieldValuedPointPullbackResidueFieldAlgebra
    (f : X ⟶ Y) {k : Type u} [Field k]
    (g : Spec (CommRingCat.of k) ⟶ Y) (x : (pullback f g : Scheme)) :
    Algebra k ((pullback f g : Scheme).residueField x) :=
  ResidueField.algebraOfSpec (pullback.snd f g) x

/-- The degree over the source field of the residue field at a point of a field-valued
pullback. -/
noncomputable abbrev fieldValuedPointPullbackResidueDegree
    (f : X ⟶ Y) {k : Type u} [Field k]
    (g : Spec (CommRingCat.of k) ⟶ Y) (x : (pullback f g : Scheme)) : ℕ :=
  Module.finrank k ((pullback f g : Scheme).residueField x)

/-- A natural number bounds all fibre degrees of a scheme morphism if and only if it bounds
the degree of every finite pullback along a field-valued point. -/
theorem degreesOfFibresBoundedBy_iff_forall_fieldValuedPoints (f : X ⟶ Y) (n : ℕ) :
    degreesOfFibresBoundedBy f n ↔
      ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
        IsFinite (pullback.snd f g) ∧ fieldValuedPointPullbackDegree f g ≤ n := sorry

/-- If every field-valued pullback of a scheme morphism is finite with uniformly bounded
degree, then the morphism has universally bounded fibres. -/
theorem universallyBoundedFibres_of_forall_fieldValuedPoints
    {f : X ⟶ Y} {n : ℕ}
    (h : ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
      IsFinite (pullback.snd f g) ∧ fieldValuedPointPullbackDegree f g ≤ n) :
    universallyBoundedFibres f := by
  exact ⟨n, (degreesOfFibresBoundedBy_iff_forall_fieldValuedPoints f n).2 h⟩

/-- A fibre-degree bound makes every field-valued pullback finite and bounds its number of
points. -/
theorem degreesOfFibresBoundedBy.finite_pullback_and_natCard_le
    {f : X ⟶ Y} {n : ℕ} (h : degreesOfFibresBoundedBy f n)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y) :
    Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n := sorry

/-- A fibre-degree bound bounds the sum of residue degrees over any exhaustive finite set of
points of a field-valued pullback. -/
theorem degreesOfFibresBoundedBy.sum_fieldValuedPointPullbackResidueDegree_le
    {f : X ⟶ Y} {n : ℕ} (h : degreesOfFibresBoundedBy f n)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y)
    (s : Finset (pullback f g : Scheme)) (hs : ∀ x, x ∈ s) :
    ∑ x ∈ s, fieldValuedPointPullbackResidueDegree f g x ≤ n := sorry

end Scheme.Hom
end AlgebraicGeometry
