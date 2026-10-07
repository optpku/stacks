module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Example_98_22_4_Key_example_Obstruction

/-!
# Example 98.22.4 (Key example)

The slice `𝒳 = (Sch/X)_fppf` of an affine finite-type morphism `X = Spec(R) → Spec(Λ)`
with `R = Λ[ι]/J` carries the naive cotangent obstruction theory of
`Algebra.NaiveCotangent.Obstruction`.

@stack 07YI
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Algebra
open Algebra.Generators
open Algebra.Extension
open scoped NaiveCotangent

noncomputable section

universe u

namespace Algebra.NaiveCotangent.Obstruction

variable {Λ ι : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (J : Ideal (MvPolynomial ι Λ))

/-- The slice `𝒳 = (Sch/Spec(R))_fppf` of `X = Spec(R)` over `S = Spec(Λ)`. -/
abbrev presentedSlice {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    GroupoidsOver (Spec (CommRingCat.of Λ)) :=
  GroupoidsOver.slice
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPolynomial ι Λ ⧸ J)))))

/-- `presentedSlice` is the canonical slice of `Spec(R) → Spec(Λ)`. -/
theorem presentedSlice_eq {Λ ι : Type u} [CommRing Λ] (J : Ideal (MvPolynomial ι Λ)) :
    presentedSlice J =
      GroupoidsOver.slice
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (MvPolynomial ι Λ ⧸ J))))) :=
  sorry

/-- Example 98.22.4 (Key example) (1): the naive cotangent complex `NL{R⁄Λ}` is
canonically homotopy equivalent to the two-term presentation complex
`J/J² ⟶ ⊕ R d x_i` of `Generators.naive`. -/
@[stacks 07YI]
def homotopyEquiv_presentation :
    HomotopyEquiv
      (NL{(MvPolynomial ι Λ ⧸ J) ⁄ Λ})
      (Extension.NaiveCotangent.complex (presentation J).toExtension) :=
  homotopyEquiv J

/-- The labeled homotopy equivalence is the canonical generators comparison. -/
theorem homotopyEquiv_presentation_eq :
    homotopyEquiv_presentation J =
      Extension.NaiveCotangent.generatorsHomotopyEquiv
        (Generators.self Λ (MvPolynomial ι Λ ⧸ J)) (presentation J) :=
  sorry

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable [Algebra Λ A'] [Algebra Λ A]
variable (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
variable (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)

/-- Example 98.22.4 (Key example) (2): the obstruction module of a deformation situation
`(x, A' → A)` is `Hom_R(J/J², I) / Hom_R(R^{⊕ι}, I)`, equivalently
`Ext¹_R(NL{R⁄Λ}, I)`, equivalently `Ext¹_A(NL{R⁄Λ} ⊗_R A, I)`. -/
@[stacks 07YI]
theorem obstructionModule_spec :
    Function.Bijective (homCokerEquiv π J φ).toLinearMap ∧
      Function.Bijective (extEquiv π J φ).toLinearMap ∧
      Function.Bijective (baseChangeExtEquiv π J φ).toLinearMap :=
  sorry

/-- Example 98.22.4 (Key example) (3): the obstruction class is the class of
`f ↦ f(a')` for any lifts of the coordinates, and is independent of those lifts. -/
@[stacks 07YI]
theorem obstruction_ofLifts_independent (a' : ι → A')
    (ha' : ∀ i, π (a' i) = φ ((presentation J).val i)) :
    obstruction π J φ = ofLifts π J φ a' ha' :=
  sorry

/-- Example 98.22.4 (Key example) (4): the class vanishes if and only if `x` lifts through
`A' → A`, so the slice `(Sch/Spec(R))_fppf` over `Spec(Λ)` obtains an obstruction theory. -/
@[stacks 07YI]
theorem obstruction_eq_zero_iff_hasLift :
    obstruction π J φ = 0 ↔ AlgHom.HasLift π φ :=
  sorry

/-- Example 98.22.4 (Key example) (5): the obstruction class is functorial in morphisms of
square-zero deformation situations. -/
@[stacks 07YI]
theorem obstruction_map {B' B : Type u} [CommRing B'] [CommRing B]
    [Algebra Λ B'] [Algebra Λ B]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) (hφψ : ψ = σ.comp φ) :
    map π ρ J φ ψ τ σ hcomm hφψ (obstruction π J φ) = obstruction ρ J ψ :=
  sorry

/-- Example 98.22.4 (Key example) (6): the obstruction class is the composition
`NL{R⁄Λ} ⟶ NL{A⁄Λ} ⟶ NL{A⁄A'} ⟶ I[1]` in `D(A)`. -/
@[stacks 07YI]
theorem obstruction_eq_composition :
    baseChangeExtEquiv π J φ (obstruction π J φ) = composition π J φ :=
  sorry

end Algebra.NaiveCotangent.Obstruction

end
