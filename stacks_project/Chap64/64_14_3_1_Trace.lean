/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import stacks_project.Chap64.«64_14_3_1_Stalk»
public import stacks_project.Chap64.Proposition_64_10_2_Trace

/-!
# Geometric Frobenius traces on stalks

This leaf owns the local Lefschetz trace sum
`∑_{x ∈ X(k)} Tr(π_X | K_x̄)`, valued in `Λ♮`. The global trace is
`globalLefschetzNumber`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [CommRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Local Lefschetz trace sum `∑_{x ∈ X(k)} Tr(π_X | K_x̄)` in `Λ♮`. -/
noncomputable def traceGeometricFrobeniusStalks (X : SchemeOverField k)
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) : Λ♮ :=
  ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
    (hK x).traceNatural (geometricFrobeniusDerivedStalk K x)

/-- Unfolding of the stalk-side trace as a finitely supported sum of traces of
geometric Frobenius on derived geometric stalks. -/
theorem traceGeometricFrobeniusStalks_spec (X : SchemeOverField k)
    (K : EtaleDerived X.left Λ)
    (hK : ∀ x : (𝟙_ (SchemeOverField k) ⟶ X),
      DerivedCategory.IsPerfect (geometricDerivedStalk K x)) :
    traceGeometricFrobeniusStalks X K hK =
      ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
        (hK x).traceNatural (geometricFrobeniusDerivedStalk K x) :=
  sorry

end AlgebraicGeometry.SchemeOverField
