/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_17_8_SchemeTheoreticImage

/-!
# Étale-local tests for scheme-theoretic density

An open immersion of algebraic spaces satisfies the étale-local
scheme-theoretic density tests when the scheme-theoretic closure of every
étale preimage equals the source, equivalently when some surjective étale
scheme atlas has this property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace SchemeTheoreticDensity

variable {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- For every étale morphism `φ : V ⟶ X` of algebraic spaces, the scheme-theoretic
closure of `openInverseImage φ ι` in `V` equals `V`. -/
def forallEtale : Prop :=
  ∀ {V : AlgebraicSpace S} (φ : V ⟶ X),
    Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι)

/-- `forallEtale ι` means every étale preimage of `ι` is scheme-theoretically
dominant into its source. -/
theorem forallEtale_iff : forallEtale ι ↔
    ∀ (V : AlgebraicSpace S) (φ : V ⟶ X),
      Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι) := sorry

namespace forallEtale

/-- A universal étale-preimage dominance condition witnesses `forallEtale ι`. -/
theorem of (h : ∀ {V : AlgebraicSpace S} (φ : V ⟶ X),
    Etale φ → IsSchemeTheoreticallyDominant (openInverseImageι φ ι)) :
    forallEtale ι := sorry

/-- Under `forallEtale ι`, the open inverse-image inclusion along any étale
morphism to `X` is scheme-theoretically dominant. -/
theorem spec (h : forallEtale ι) {V : AlgebraicSpace S} (φ : V ⟶ X)
    (hφ : Etale φ) : IsSchemeTheoreticallyDominant (openInverseImageι φ ι) :=
  sorry

end forallEtale

/-- There is a scheme `V` over `S` and a surjective étale morphism `φ` from
`ofOver V` to `X` whose open inverse-image inclusion is scheme-theoretically
dominant. -/
def existsSurjectiveEtale : Prop :=
  ∃ (V : Over S) (φ : ofOver V ⟶ X),
    Etale φ ∧ Surjective φ ∧ IsSchemeTheoreticallyDominant (openInverseImageι φ ι)

/-- `existsSurjectiveEtale ι` is the existence of a surjective étale scheme atlas
of `X` along which the open inverse image of `ι` is scheme-theoretically
dominant. -/
theorem existsSurjectiveEtale_iff : existsSurjectiveEtale ι ↔
    ∃ (V : Over S) (φ : ofOver V ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsSchemeTheoreticallyDominant (openInverseImageι φ ι) := sorry

namespace existsSurjectiveEtale

/-- A surjective étale scheme atlas of `X` along which the open inverse image of
`ι` is scheme-theoretically dominant witnesses `existsSurjectiveEtale ι`. -/
theorem of {V : Over S} (φ : ofOver V ⟶ X) [Etale φ] [Surjective φ]
    (h : IsSchemeTheoreticallyDominant (openInverseImageι φ ι)) :
    existsSurjectiveEtale ι := sorry

/-- `existsSurjectiveEtale ι` supplies a surjective étale scheme atlas of `X`
along which the open inverse image of `ι` is scheme-theoretically dominant. -/
theorem spec (h : existsSurjectiveEtale ι) :
    ∃ (V : Over S) (φ : ofOver V ⟶ X),
      Etale φ ∧ Surjective φ ∧
        IsSchemeTheoreticallyDominant (openInverseImageι φ ι) := sorry

end existsSurjectiveEtale

end SchemeTheoreticDensity

end AlgebraicGeometry.AlgebraicSpace
