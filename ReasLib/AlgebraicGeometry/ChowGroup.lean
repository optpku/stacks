module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Finiteness
public import ReasLib.Topology.Specialization.Dimension

/-!
# Rational equivalence and Chow groups

This file defines locally finite sums of pushed-forward principal cycles, rational equivalence,
and Chow groups of cycles of a fixed dimension.
-/

@[expose] public section

open CategoryTheory Function Set Topology

noncomputable section

universe u v

namespace AlgebraicGeometry

namespace RationalEquivalence

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)

/-- The pushforward to `X` of a principal cycle on the reduced closure of a point of
dimension `k + 1` is a degree-`k` cycle. -/
theorem principal_mem_dimensionSubgroup (x : X) (hx : d x = k + 1)
    (f : (Scheme.PointClosure.scheme x).functionFieldˣ) :
    AlgebraicCycle.map (Scheme.PointClosure.ι x)
      (fun y ↦ d (Scheme.PointClosure.ι x y)) d
      (AlgebraicCycle.principal (Scheme.PointClosure.scheme x) f) ∈
        AlgebraicCycle.dimensionSubgroup d k := sorry

/-- The degree-`k` boundary obtained by pushing a principal cycle on the reduced closure of a
point of dimension `k + 1` into `X`. -/
noncomputable def principal (x : X) (hx : d x = k + 1)
    (f : (Scheme.PointClosure.scheme x).functionFieldˣ) : CycleGroup X d k :=
  ⟨AlgebraicCycle.map (Scheme.PointClosure.ι x)
      (fun y ↦ d (Scheme.PointClosure.ι x y)) d
      (AlgebraicCycle.principal (Scheme.PointClosure.scheme x) f),
    principal_mem_dimensionSubgroup d k x hx f⟩

/-- The support of a pushed-forward principal cycle lies in the corresponding point closure. -/
theorem principal_support (x : X) (hx : d x = k + 1)
    (f : (Scheme.PointClosure.scheme x).functionFieldˣ) :
    (CycleGroup.toAlgebraicCycle d k (principal d k x hx f)).support ⊆
      (Scheme.PointClosure.closedSubset x : Set X) := sorry

/-- Principal cycles attached to a locally finite family of point closures have locally finite
supports. -/
theorem locallyFinite_principal_support {J : Type v} (x : J → X)
    (hx : ∀ j, d (x j) = k + 1)
    (f : ∀ j, (Scheme.PointClosure.scheme (x j)).functionFieldˣ)
    (hlocal : LocallyFinite fun j ↦ (Scheme.PointClosure.closedSubset (x j) : Set X)) :
    LocallyFinite fun j ↦
      (CycleGroup.toAlgebraicCycle d k (principal d k (x j) (hx j) (f j))).support := sorry

/-- The locally finite sum of pushed-forward principal cycles associated to a family of
dimension-`k + 1` point closures. -/
noncomputable def boundary {J : Type v} (x : J → X)
    (hx : ∀ j, d (x j) = k + 1)
    (f : ∀ j, (Scheme.PointClosure.scheme (x j)).functionFieldˣ)
    (hlocal : LocallyFinite fun j ↦ (Scheme.PointClosure.closedSubset (x j) : Set X)) :
    CycleGroup X d k :=
  CycleGroup.locallyFiniteSum d k (fun j ↦ principal d k (x j) (hx j) (f j))
    (locallyFinite_principal_support d k x hx f hlocal)

/-- A boundary coefficient is the pointwise finite sum of the corresponding principal-cycle
coefficients. -/
theorem boundary_apply {J : Type v} (x : J → X)
    (hx : ∀ j, d (x j) = k + 1)
    (f : ∀ j, (Scheme.PointClosure.scheme (x j)).functionFieldˣ)
    (hlocal : LocallyFinite fun j ↦ (Scheme.PointClosure.closedSubset (x j) : Set X))
    (z : X) :
    CycleGroup.toAlgebraicCycle d k (boundary d k x hx f hlocal) z =
      ∑ᶠ j, CycleGroup.toAlgebraicCycle d k (principal d k (x j) (hx j) (f j)) z := sorry

/-- A degree-`k` cycle is rationally trivial when it is a locally finite sum of pushforwards of
principal cycles from dimension-`k + 1` point closures. -/
def IsRationallyTrivial (α : CycleGroup X d k) : Prop :=
  ∃ (J : Type u) (x : J → X) (hx : ∀ j, d (x j) = k + 1)
      (f : ∀ j, (Scheme.PointClosure.scheme (x j)).functionFieldˣ),
    ∃ hlocal : LocallyFinite fun j ↦ (Scheme.PointClosure.closedSubset (x j) : Set X),
      α = boundary d k x hx f hlocal

/-- Rational triviality is equivalent to admitting an explicit locally finite boundary
presentation. -/
theorem isRationallyTrivial_iff_exists_boundary (α : CycleGroup X d k) :
    IsRationallyTrivial d k α ↔
      ∃ (J : Type u) (x : J → X) (hx : ∀ j, d (x j) = k + 1)
          (f : ∀ j, (Scheme.PointClosure.scheme (x j)).functionFieldˣ),
        ∃ hlocal : LocallyFinite fun j ↦ (Scheme.PointClosure.closedSubset (x j) : Set X),
          α = boundary d k x hx f hlocal := sorry

/-- The zero cycle is rationally trivial. -/
theorem zero_isRationallyTrivial :
    IsRationallyTrivial d k (0 : CycleGroup X d k) := sorry

/-- A sum of rationally trivial cycles is rationally trivial. -/
theorem add_isRationallyTrivial {a b : CycleGroup X d k}
    (ha : IsRationallyTrivial d k a) (hb : IsRationallyTrivial d k b) :
    IsRationallyTrivial d k (a + b) := sorry

/-- The negative of a rationally trivial cycle is rationally trivial. -/
theorem neg_isRationallyTrivial {a : CycleGroup X d k}
    (ha : IsRationallyTrivial d k a) : IsRationallyTrivial d k (-a) := sorry

/-- The additive subgroup of rationally trivial degree-`k` cycles. -/
def boundaries : AddSubgroup (CycleGroup X d k) where
  carrier := IsRationallyTrivial d k
  zero_mem' := zero_isRationallyTrivial d k
  add_mem' := add_isRationallyTrivial d k
  neg_mem' := neg_isRationallyTrivial d k

/-- Membership in the boundary subgroup is rational triviality. -/
theorem mem_boundaries_iff (α : CycleGroup X d k) :
    α ∈ boundaries d k ↔ IsRationallyTrivial d k α := sorry

/-- Two degree-`k` cycles are rationally equivalent when their difference is rationally
trivial. -/
def RationallyEquivalent (α β : CycleGroup X d k) : Prop :=
  α - β ∈ boundaries d k

/-- Rational equivalence is membership of the difference in the boundary subgroup. -/
theorem rationallyEquivalent_iff_sub_mem (α β : CycleGroup X d k) :
    RationallyEquivalent d k α β ↔ α - β ∈ boundaries d k := sorry

end RationalEquivalence

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)

/-- The Chow group of degree-`k` cycles modulo rational equivalence. -/
abbrev ChowGroup (X : Scheme.{u}) [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ) :
    Type u :=
  CycleGroup X d k ⧸ RationalEquivalence.boundaries d k

/-- The canonical quotient homomorphism from degree-`k` cycles to their Chow group. -/
abbrev chowClass : CycleGroup X d k →+ ChowGroup X d k :=
  QuotientAddGroup.mk' (RationalEquivalence.boundaries d k)

/-- The quotient map from cycles to Chow classes is surjective. -/
theorem chowClass_surjective : Function.Surjective (chowClass d k) := sorry

/-- A cycle has zero Chow class exactly when it is rationally trivial. -/
theorem chowClass_eq_zero_iff (α : CycleGroup X d k) :
    chowClass d k α = 0 ↔ RationalEquivalence.IsRationallyTrivial d k α := sorry

/-- Rational equivalence is equality of Chow classes. -/
theorem RationalEquivalence.rationallyEquivalent_iff_chowClass_eq
    (α β : CycleGroup X d k) :
    RationalEquivalence.RationallyEquivalent d k α β ↔
      chowClass d k α = chowClass d k β := sorry

end AlgebraicGeometry
