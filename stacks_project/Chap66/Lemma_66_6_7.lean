module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair.FiniteFibers
import StacksCheckRecall

/-!
# Finite fibres of étale morphisms with quasi-compact kernel-pair projections

An étale morphism from a scheme to an algebraic space, whose represented kernel-pair
projections are quasi-compact, has finite fibres on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/- Lemma 66.6.7 (1): an étale morphism from a scheme to an algebraic space has finite
fibres on points when both represented kernel-pair projections are quasi-compact. -/
@[stacks 03IJ] #check
  (AlgebraicGeometry.AlgebraicSpace.pointsMap_finite_preimage_singleton :
    ∀ (φ : AlgebraicSpace.ofOver U ⟶ X)
      (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ),
      AlgebraicGeometry.QuasiCompact (AlgebraicSpace.kernelPair φ hφ.rep).t.left →
      AlgebraicGeometry.QuasiCompact (AlgebraicSpace.kernelPair φ hφ.rep).s.left →
      ∀ (x : AlgebraicSpace.Points X), (AlgebraicSpace.Points.map φ ⁻¹' {x}).Finite)

/- Lemma 66.6.7 (2): the canonical morphism from the represented kernel pair to the
algebraic space also has finite fibres on points under the same hypotheses. -/
@[stacks 03IJ] #check
  (AlgebraicGeometry.AlgebraicSpace.kernelPairHom_pointsMap_finite_preimage_singleton :
    ∀ (φ : AlgebraicSpace.ofOver U ⟶ X)
      (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ),
      AlgebraicGeometry.QuasiCompact (AlgebraicSpace.kernelPair φ hφ.rep).t.left →
      AlgebraicGeometry.QuasiCompact (AlgebraicSpace.kernelPair φ hφ.rep).s.left →
      ∀ (x : AlgebraicSpace.Points X),
        (AlgebraicSpace.Points.map (AlgebraicSpace.kernelPairHom φ hφ) ⁻¹' {x}).Finite)

/- Quasi-compactness of the étale morphism implies finiteness of its fibres on points. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.pointsMap_finite_preimage_singleton_of_quasiCompact :
    ∀ (φ : AlgebraicSpace.ofOver U ⟶ X)
      (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ),
      (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ →
      ∀ (x : AlgebraicSpace.Points X), (AlgebraicSpace.Points.map φ ⁻¹' {x}).Finite)

/- Quasi-compactness of the étale morphism also gives finite fibres for the kernel pair. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.kernelPairHom_pointsMap_finite_preimage_singleton_of_quasiCompact :
    ∀ (φ : AlgebraicSpace.ofOver U ⟶ X)
      (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ),
      (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ →
      ∀ (x : AlgebraicSpace.Points X),
        (AlgebraicSpace.Points.map (AlgebraicSpace.kernelPairHom φ hφ) ⁻¹' {x}).Finite)
