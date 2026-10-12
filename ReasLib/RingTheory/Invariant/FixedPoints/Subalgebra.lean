/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Inclusions between fixed subalgebras

This leaf packages the contravariant map on fixed subalgebras induced by an inclusion of
acting subgroups.  The construction is independent of a particular field or integral-closure
argument and is therefore useful throughout invariant theory.
@stack 0BU6
-/

universe u v w

namespace FixedPoints

section Action

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommSemiring A] [CommSemiring B] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The ambient action is invariant over its fixed subalgebra. -/
@[stacks 0BU6 "fixed subalgebra ambient invariant structure"]
instance subalgebra_isInvariant :
    Algebra.IsInvariant (FixedPoints.subalgebra A B G) B G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

end Action

variable {A : Type u} {B : Type v} {G : Type w}
variable [CommSemiring A] [CommSemiring B] [Algebra A B]
variable [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- An inclusion of acting subgroups reverses the inclusion of their fixed subalgebras. -/
@[stacks 0BU6 "fixed subalgebra inclusion along subgroup inclusion"]
theorem subalgebra_le_of_le {H H' : Subgroup G} (h : H ≤ H') :
    FixedPoints.subalgebra A B H' ≤ FixedPoints.subalgebra A B H := sorry

-- Proof strategy: take an `H'`-fixed element and an element `g : H`; apply its fixedness to
-- `h g.2 : g.1 ∈ H'`.  The carrier and scalar structures of both fixed subalgebras are inherited
-- from `B`, so subtype extensionality closes the inclusion.

/-- The canonical algebra map between fixed subalgebras induced by a subgroup inclusion. -/
@[reducible, stacks 0BU6 "fixed subalgebra algebra map along subgroup inclusion"]
def subalgebraAlgebraOfLe {H H' : Subgroup G} (h : H ≤ H') :
    Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
  ((Subalgebra.inclusion (subalgebra_le_of_le h)).toRingHom).toAlgebra

/-- The algebra map of `subalgebraAlgebraOfLe` is the canonical fixed-subalgebra inclusion. -/
@[stacks 0BU6 "algebra map of the fixed-subalgebra inclusion"]
theorem algebraMap_subalgebraAlgebraOfLe {H H' : Subgroup G} (h : H ≤ H') :
    @algebraMap (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) _ _
        (subalgebraAlgebraOfLe h) =
      (Subalgebra.inclusion (subalgebra_le_of_le h)).toRingHom := sorry

-- Proof strategy: unfold `subalgebraAlgebraOfLe`; the algebra map of the resulting
-- `RingHom.toAlgebra` is the displayed `Subalgebra.inclusion`.

/-- A nested fixed-subalgebra contraction lies over the contraction at the larger fixed
subalgebra. -/
@[stacks 0BU6 "nested fixed-subalgebra contraction lies over"]
theorem under_liesOver_under_of_le {H H' : Subgroup G} (h : H ≤ H') (m : Ideal B) :
    -- Local instance justification (defeq pin): this contraction comparison must use the canonical fixed-subalgebra inclusion selected by `subalgebraAlgebraOfLe`.
    letI : Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
      subalgebraAlgebraOfLe h
    (m.under (FixedPoints.subalgebra A B H)).LiesOver
      (m.under (FixedPoints.subalgebra A B H')) := sorry

-- Proof strategy: rewrite the named algebra map with
-- `algebraMap_subalgebraAlgebraOfLe`; both ideals are contractions of `m`, so membership
-- extensionality and `Ideal.mem_comap` identify the lower contraction with the contraction of the
-- upper one.

/-- The canonical inclusions associated to `H ≤ H'` form the scalar tower
`B ^ H' → B ^ H → B`. -/
@[stacks 0BU6 "scalar tower for nested fixed subalgebras"]
theorem subalgebra_isScalarTower_of_le {H H' : Subgroup G} (h : H ≤ H') :
    -- Local instance justification (defeq pin): this scalar tower must use the canonical fixed-subalgebra inclusion selected by `subalgebraAlgebraOfLe`.
    letI : Algebra (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) :=
      subalgebraAlgebraOfLe h
    IsScalarTower (FixedPoints.subalgebra A B H') (FixedPoints.subalgebra A B H) B := sorry

-- Proof strategy: rewrite the intermediate algebra map with
-- `algebraMap_subalgebraAlgebraOfLe` and verify the scalar-tower algebra-map identity after
-- coercion to `B`; all maps are canonical subtype inclusions.

/-- Canonical inclusions along `H₁ ≤ H₂ ≤ H₃` form the scalar tower
`B ^ H₃ → B ^ H₂ → B ^ H₁`. -/
@[stacks 0BU6 "scalar tower for three nested fixed subalgebras"]
theorem subalgebra_isScalarTower_of_le_of_le
    {H₁ H₂ H₃ : Subgroup G} (h₁₂ : H₁ ≤ H₂) (h₂₃ : H₂ ≤ H₃) :
    -- Local instance justification (defeq pin): this upper-to-middle map must be the canonical fixed-subalgebra inclusion selected by `subalgebraAlgebraOfLe`.
    letI : Algebra (FixedPoints.subalgebra A B H₃) (FixedPoints.subalgebra A B H₂) :=
      subalgebraAlgebraOfLe h₂₃
    -- Local instance justification (defeq pin): this middle-to-lower map must be the canonical fixed-subalgebra inclusion selected by `subalgebraAlgebraOfLe`.
    letI : Algebra (FixedPoints.subalgebra A B H₂) (FixedPoints.subalgebra A B H₁) :=
      subalgebraAlgebraOfLe h₁₂
    -- Local instance justification (defeq pin): this composite map must be the canonical fixed-subalgebra inclusion selected by `subalgebraAlgebraOfLe`.
    letI : Algebra (FixedPoints.subalgebra A B H₃) (FixedPoints.subalgebra A B H₁) :=
      subalgebraAlgebraOfLe (h₁₂.trans h₂₃)
    IsScalarTower (FixedPoints.subalgebra A B H₃)
      (FixedPoints.subalgebra A B H₂) (FixedPoints.subalgebra A B H₁) := sorry

-- Proof strategy: with the three displayed inclusion algebras installed, use
-- `IsScalarTower.of_algebraMap_eq'`; rewrite each algebra map by
-- `algebraMap_subalgebraAlgebraOfLe` and prove equality by subtype extensionality.

section Ring

variable {R : Type u} {S : Type v} {Γ : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [Group Γ] [MulSemiringAction Γ S] [SMulCommClass Γ R S]

/-- A finite acting group makes the ambient algebra integral over its fixed subalgebra. -/
@[stacks 0BU6 "integrality over a finite-group fixed subalgebra"]
instance subalgebra_isIntegral [Finite Γ] :
    Algebra.IsIntegral (FixedPoints.subalgebra R S Γ) S := sorry

-- Proof strategy: transport `FixedPoints.subring_isIntegral` across the equality of the
-- fixed-subalgebra and fixed-subring carriers.  Equivalently, reuse the same finite-orbit monic
-- polynomial over the fixed subalgebra and map its coefficients through the canonical inclusion.

end Ring

end FixedPoints
