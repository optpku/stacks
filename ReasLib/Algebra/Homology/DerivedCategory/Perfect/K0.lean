module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective.K0
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Subcategory
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.K0.GrothendieckGroup
import Mathlib.Tactic.CrossRefAttribute

/-!
# K₀ of perfect derived modules

This leaf owns the source-facing Euler-characteristic map and the additive K₀ comparison
interface for perfect derived `R`-modules.  Existence and independence arguments remain Prop
statements, so no proof-dependent choice is exported as a canonical datum.

@stack 0AFY
@stack 0FCU
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace CategoryTheory

variable (R : Type u) [Ring R]

/-- The source-facing predicate that a class is represented by a bounded finite-projective
complex. -/
@[stacks 0AFY "Euler characteristic represented by a finite-projective complex"]
def IsEulerCharacteristicValue (K : PerfectDerived R)
    (c : ModuleCat.K0.projective R) : Prop :=
  ∃ (L : CochainComplex (ModuleCat R) ℤ) (_ : K.obj ≅ DerivedCategory.Q.obj L)
    (_ : CochainComplex.IsBoundedFiniteProjective L),
    c = L.eulerCharacteristic

/-- A map on perfect objects satisfying the three source clauses for an Euler characteristic. -/
@[stacks 0AFY "Euler characteristic map on perfect derived objects"]
structure EulerCharacteristicMap (R : Type u) [Ring R] where
  /-- The class assigned to a perfect derived object. -/
  value : PerfectDerived R → ModuleCat.K0.projective R
  /-- The class changes by `n.negOnePow` under a cohomological shift. -/
  shift : ∀ (K : PerfectDerived R) (n : ℤ),
    value (K⟦n⟧) = n.negOnePow • value K
  /-- The class is additive on distinguished triangles of perfect objects. -/
  triangle : ∀ {T : Triangle (PerfectDerived R)}, T ∈ distTriang (PerfectDerived R) →
    value T.obj₂ = value T.obj₁ + value T.obj₃
  /-- The value agrees with the alternating sum of every bounded finite-projective representative.
  -/
  representative : ∀ (K : PerfectDerived R) (c : ModuleCat.K0.projective R),
    IsEulerCharacteristicValue R K c → value K = c

/-- Lemma 15.120.1 (0AFY): an Euler-characteristic map with shift, triangle, and representative
properties exists for perfect derived `R`-modules. -/
@[stacks 0AFY "Lemma 15.120.1, Euler characteristic map"]
theorem exists_eulerCharacteristicMap : Nonempty (EulerCharacteristicMap R) := sorry
-- Proof strategy: assign to each perfect object the Euler class of a bounded finite-projective
-- representative; prove independence with `CochainComplex.eulerCharacteristic_eq_of_quasiIso`,
-- then obtain the shift and triangle laws from the shifted representative and mapping-cone
-- formulas and discharge `representative` by the same independence theorem.

/-- The zeroth Grothendieck group of the perfect derived category of `R`. -/
@[stacks 0FCU "Grothendieck group of perfect derived modules"]
abbrev PerfectK0 (R : Type u) [Ring R] : Type (u + 1) :=
  TriangulatedK0 (PerfectDerived R)

/-- An additive comparison between the perfect-derived and projective module K₀ groups. -/
@[stacks 0FCU "comparison of perfect-derived and projective K₀"]
structure K0Comparison (R : Type u) [Ring R] where
  /-- The homomorphism induced by the Euler characteristic. -/
  map : PerfectK0 R →+ ModuleCat.K0.projective R
  /-- The inverse homomorphism given by degree-zero perfect modules. -/
  inverse : ModuleCat.K0.projective R →+ PerfectK0 R
  /-- The inverse is a left inverse of the comparison map. -/
  left_inverse : Function.LeftInverse inverse map
  /-- The inverse is a right inverse of the comparison map. -/
  right_inverse : Function.RightInverse inverse map

/-- Lemma 15.120.2 (0FCU): the perfect-derived K₀ group is additively equivalent to the
projective-module K₀ group. -/
@[stacks 0FCU "Lemma 15.120.2, perfect-derived K₀ comparison"]
theorem exists_K0Comparison : Nonempty (K0Comparison R) := sorry
-- Proof strategy: descend an Euler-characteristic map through `TriangulatedK0.lift`; construct the
-- inverse from degree-zero finite-projective modules through the projective Grothendieck-group
-- universal property, and verify both inverse laws on the respective object generators using the
-- representative and triangle relations.

/-- The comparison homomorphism in a `K0Comparison` is bijective. -/
@[stacks 0FCU "bijectivity of the K₀ comparison"]
theorem K0Comparison.bijective (h : K0Comparison R) : Function.Bijective h.map := sorry
-- Proof strategy: derive injectivity from `h.left_inverse.injective` and surjectivity from
-- `h.right_inverse.surjective`.

/-- The additive equivalence carried by a `K0Comparison`. -/
@[stacks 0FCU "perfect-derived and projective K₀ equivalence"]
noncomputable def K0Comparison.equiv (h : K0Comparison R) :
    PerfectK0 R ≃+ ModuleCat.K0.projective R :=
  { toFun := h.map
    invFun := h.inverse
    left_inv := h.left_inverse
    right_inv := h.right_inverse
    map_add' := h.map.map_add }

end CategoryTheory

end
