module

public import stacks_project.Chap67.Lemma_67_17_2_SchemeTheoreticDensity

/-!
# Scheme-theoretic density of open immersions of algebraic spaces

An open immersion of algebraic spaces is scheme-theoretically dense when it
satisfies the étale-local tests of Lemma 67.17.2: every étale preimage
inclusion is scheme-theoretically dominant, equivalently some surjective étale
scheme atlas has this property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open immersion of algebraic spaces is scheme-theoretically dense when
every étale preimage inclusion is scheme-theoretically dominant. -/
@[mk_iff]
class IsSchemeTheoreticallyDense {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] : Prop where
  /-- Every étale preimage of `ι` is scheme-theoretically dominant into its source. -/
  forallEtale : SchemeTheoreticDensity.forallEtale ι

namespace IsSchemeTheoreticallyDense

/-- The identity morphism of an algebraic space is scheme-theoretically dense. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsSchemeTheoreticallyDense (𝟙 X) := sorry

/-- An open immersion that is an isomorphism is scheme-theoretically dense. -/
instance of_isIso {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [IsOpenImmersion ι] [IsIso ι] : IsSchemeTheoreticallyDense ι := sorry

/-- The universal étale-preimage dominance test witnesses scheme-theoretic density. -/
theorem of {S : Scheme.{u}} {X U : AlgebraicSpace S} {ι : U ⟶ X}
    [IsOpenImmersion ι] (h : SchemeTheoreticDensity.forallEtale ι) :
    IsSchemeTheoreticallyDense ι := sorry

/-- A scheme-theoretically dense open immersion satisfies the universal
étale-preimage dominance test. -/
theorem spec {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι] :
    SchemeTheoreticDensity.forallEtale ι := sorry

/-- Scheme-theoretic density of an open immersion is equivalent to the existence
of a surjective étale scheme atlas along which the open inverse image is
scheme-theoretically dominant. -/
theorem iff_existsSurjectiveEtale {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (ι : U ⟶ X) [IsOpenImmersion ι] :
    IsSchemeTheoreticallyDense ι ↔
      SchemeTheoreticDensity.existsSurjectiveEtale ι := sorry

end IsSchemeTheoreticallyDense

end AlgebraicGeometry.AlgebraicSpace
