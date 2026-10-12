/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Proposition_42_57_1_ChernCap
public import stacks_project.Chap42.Proposition_42_57_1_Filtration

/-!
# Proposition 42.57.1

The composition of `ℱ ↦ ℱ[0]`, localized Chern character, and cap against `[Y]`
induces `K₀'(X) ⊗ ℚ ≃ CH_*(X) ⊗ ℚ`, depending on the regular quasi-compact
ambient `Y`. Independently, the canonical map `CH_k(X) ⊗ ℚ → gr_k K₀'(X) ⊗ ℚ` is
an isomorphism of `ℚ`-vector spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ChowGroup AlgebraicGeometry.Scheme.K0'
open AlgebraicGeometry.Scheme.K0WithSupport
open scoped TensorProduct

noncomputable section

universe u

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
variable (i : X ⟶ Y) [IsClosedImmersion i.left] [Scheme.Regular Y.left]
variable [CompactSpace Y.left]

include i

/-- Proposition 42.57.1 (1): In Situation 42.7.1, a closed immersion `X ⟶ Y` of schemes
locally of finite type over `S` with `Y` regular and quasi-compact induces, via
`ℱ ↦ ℱ[0]`, the localized Chern character `ch(X ⟶ Y, -)`, and `c ↦ c ∩ [Y]`, an
isomorphism `K₀'(X) ⊗ ℚ ⟶ CH_*(X) ⊗ ℚ` depending on the choice of `Y`. -/
@[stacks 0FEW]
theorem toRationalChow_bijective (classes : ChernClass.Theory δ Y.hom) :
    Function.Bijective
      ((AddEquiv.toAddMonoidHom
          (rationalChow.congrHom δ (i.left ≫ Y.hom) (Over.w i))).comp
        (toRationalChow_tensorQ δ i.left irreducibleComponent_isCompact classes
          (toRationalChow_finiteSupport δ i.left
            irreducibleComponent_isCompact classes))) :=
  sorry

/-- Proposition 42.57.1 (2): In the same situation, the canonical map
`CH_k(X) ⊗ ℚ ⟶ gr_k K₀'(X) ⊗ ℚ` is an isomorphism of `ℚ`-vector spaces for every
`k ∈ ℤ`. -/
@[stacks 0FEW]
theorem toGradedK0'_bijective (k : ℤ) :
    Function.Bijective (toGradedK0'_tensorQ X.hom δ k) :=
  sorry


