module

public import ReasLib.Algebra.Ring.Subring.Intersection
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair.DimensionOne
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite families of subrings with a common fraction field

This leaf owns the intersection and pairwise tensor comparison maps of a
finite nonempty family of subrings of a common field.  Scheme-theoretic
consequences of these maps live in the corresponding `Spec` leaf.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace FractionRing.SubringFamily

variable {K : Type u} [Field K]
variable {ι : Type v}

/-- The intersection of all component subrings of a family in a common ambient field. -/
def intersection (A : ι → Subring K) : Subring K :=
  sInf (Set.range A)

/-- Membership in the family intersection is membership in every component subring. -/
theorem mem_intersection_iff (A : ι → Subring K) {x : K} :
    x ∈ intersection A ↔ ∀ i, x ∈ A i := sorry

/-- The canonical inclusion of the family intersection into a component subring. -/
def toComponent (A : ι → Subring K) (i : ι) : intersection A →+* A i :=
  Subring.inclusion (sInf_le (Set.mem_range_self i))

/-- The family intersection is contained in each component subring. -/
theorem intersection_le_component (A : ι → Subring K) (i : ι) :
    intersection A ≤ A i := sorry

/-- A component inclusion preserves its element in the ambient field. -/
@[simp]
theorem coe_toComponent (A : ι → Subring K) (i : ι) (x : intersection A) :
    ((toComponent A i x : A i) : K) = x := sorry

/-- The family intersection acts on each component through the canonical inclusion. -/
instance instAlgebraIntersectionComponent (A : ι → Subring K) (i : ι) :
    Algebra (intersection A) (A i) :=
  (toComponent A i).toAlgebra

/-- The intersection-component-ambient inclusions form a scalar tower. -/
instance instIsScalarTowerIntersectionComponentAmbient (A : ι → Subring K) (i : ι) :
    IsScalarTower (intersection A) (A i) K :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The intersection of the pair of components indexed by `i` and `j`. -/
@[reducible]
def pairIntersection (A : ι → Subring K) (i j : ι) : Subring K :=
  A i ⊓ A j

/-- The pairwise tensor comparison map from two components of a family to the ambient field. -/
def pairTensorToAmbient (A : ι → Subring K) (i j : ι) :
    A i ⊗[pairIntersection A i j] A j →ₐ[pairIntersection A i j] K :=
  Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom (pairIntersection A i j) (A i) K)
    (IsScalarTower.toAlgHom (pairIntersection A i j) (A j) K)

/-- The pairwise tensor comparison sends a pure tensor to the product of its ambient images. -/
theorem pairTensorToAmbient_apply_tmul
    (A : ι → Subring K) (i j : ι) (x : A i) (y : A j) :
    pairTensorToAmbient A i j (x ⊗ₜ[pairIntersection A i j] y) =
      algebraMap (A i) K x * algebraMap (A j) K y := sorry

/-- The condition that every component has Krull dimension one. -/
def componentsKrullDim_eq_one (A : ι → Subring K) : Prop :=
  ∀ i, ringKrullDim (A i) = 1

/-- The condition that every comparison between distinct component pairs is surjective. -/
def pairwiseTensorSurjective (A : ι → Subring K) : Prop :=
  ∀ i j, i ≠ j → Function.Surjective (pairTensorToAmbient A i j)

/-- Under the pairwise-surjective tensor hypothesis, the family intersection
is a domain and is contained in every component. -/
@[stacks 09N4]
theorem intersection_isDomain_and_le_components
    (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : componentsKrullDim_eq_one A) (hSurj : pairwiseTensorSurjective A) :
    IsDomain (intersection A) ∧ ∀ i, intersection A ≤ A i := sorry

/-- Under the pairwise-surjective tensor hypothesis, the family intersection
is Noetherian. -/
@[stacks 09N4]
theorem intersection_isNoetherian_of_pairwiseTensorSurjective
    (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : componentsKrullDim_eq_one A) (hSurj : pairwiseTensorSurjective A) :
    IsNoetherianRing (intersection A) := sorry

/-- Under the pairwise-surjective tensor hypothesis, the family intersection
has finite maximal spectrum. -/
@[stacks 09N4]
theorem intersection_finiteMaximalSpectrum_of_pairwiseTensorSurjective
    (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : componentsKrullDim_eq_one A) (hSurj : pairwiseTensorSurjective A) :
    Finite (MaximalSpectrum (intersection A)) := sorry

/-- Under the pairwise-surjective tensor hypothesis, the family intersection
has Krull dimension one. -/
@[stacks 09N4]
theorem intersection_krullDim_eq_one_of_pairwiseTensorSurjective
    (A : ι → Subring K) [Finite ι] [Nonempty ι]
    (hFraction : ∀ i, IsFractionRing (A i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (A i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (A i)))
    (hdim : componentsKrullDim_eq_one A) (hSurj : pairwiseTensorSurjective A) :
    ringKrullDim (intersection A) = 1 := sorry

end FractionRing.SubringFamily
