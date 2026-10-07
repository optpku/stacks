module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.QuasiSeparated
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair
public import stacks_project.Chap66.Lemma_66_6_5_ToSpecZ

/-!
# Quasi-separated algebraic spaces from a quasi-separated étale atlas

A surjective étale morphism from a quasi-separated scheme whose kernel-pair projections
include a quasi-compact one implies that the algebraic space is quasi-separated over `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- The comparison morphism `U ×_X U ⟶ U × U` from the represented kernel pair to the absolute
product of underlying schemes, as the product lift of the two kernel-pair projections. -/
def kernelPairToProd (φ : ofOver U ⟶ X) (hf : yoneda.relativelyRepresentable φ) :
    (kernelPair φ hf).left.left ⟶ U.left ⨯ U.left :=
  prod.lift (kernelPair φ hf).t.left (kernelPair φ hf).s.left

/-- `kernelPairToProd φ hf` is the product lift of the two kernel-pair projections. -/
theorem kernelPairToProd_eq (φ : ofOver U ⟶ X) (hf : yoneda.relativelyRepresentable φ) :
    kernelPairToProd φ hf =
      prod.lift (kernelPair φ hf).t.left (kernelPair φ hf).s.left :=
  sorry

/-- Lemma 66.6.5: let `S` be a scheme and `X` an algebraic space over `S`. If there exists a
quasi-separated scheme `U` and a surjective étale morphism `φ : ofOver U ⟶ X` such that either
kernel-pair projection is quasi-compact, then `toSpecZ X` is quasi-separated. -/
@[stacks 07S4]
theorem isQuasiSeparated_toSpecZ [QuasiSeparatedSpace U.left] (φ : ofOver U ⟶ X)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf φ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    (h_qc : QuasiCompact (kernelPair φ h_etale.rep).t.left ∨
      QuasiCompact (kernelPair φ h_etale.rep).s.left) :
    IsQuasiSeparated (toSpecZ X) :=
  sorry

/-- If the first kernel-pair projection is quasi-compact, then `toSpecZ X` is quasi-separated. -/
theorem isQuasiSeparated_toSpecZ_of_t [QuasiSeparatedSpace U.left] (φ : ofOver U ⟶ X)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf φ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    (ht : QuasiCompact (kernelPair φ h_etale.rep).t.left) :
    IsQuasiSeparated (toSpecZ X) :=
  sorry

/-- If the second kernel-pair projection is quasi-compact, then `toSpecZ X` is quasi-separated. -/
theorem isQuasiSeparated_toSpecZ_of_s [QuasiSeparatedSpace U.left] (φ : ofOver U ⟶ X)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf φ)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)
    (hs : QuasiCompact (kernelPair φ h_etale.rep).s.left) :
    IsQuasiSeparated (toSpecZ X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
