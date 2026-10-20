module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback

/-!
# Finite fibres of étale morphisms with quasi-compact kernel-pair projections

An étale morphism from a scheme to an algebraic space, whose represented kernel-pair
projections are quasi-compact, has finite fibres on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- The morphism from the represented kernel pair to the algebraic space, defined by composing
the first kernel-pair projection with the given étale morphism. -/
def kernelPairHom (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    ofOver (kernelPair φ hφ.rep).left ⟶ X :=
  ofOverMap (kernelPair φ hφ.rep).t ≫ φ

/-- `kernelPairHom φ hφ` is the composite of the first kernel-pair projection with `φ`. -/
theorem kernelPairHom_eq (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    kernelPairHom φ hφ = ofOverMap (kernelPair φ hφ.rep).t ≫ φ :=
  rfl

/-- The two kernel-pair projections become equal after composition with `φ`. -/
theorem kernelPairHom_eq_snd (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    kernelPairHom φ hφ = ofOverMap (kernelPair φ hφ.rep).s ≫ φ :=
  sorry

/-- An étale morphism from a scheme to an algebraic space has finite fibres on points if
both projections of its represented kernel pair are quasi-compact. -/
theorem pointsMap_finite_preimage_singleton (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (ht : AlgebraicGeometry.QuasiCompact (kernelPair φ hφ.rep).t.left)
    (hs : AlgebraicGeometry.QuasiCompact (kernelPair φ hφ.rep).s.left) (x : Points X) :
    (Points.map φ ⁻¹' {x}).Finite :=
  sorry

/-- The canonical morphism from the represented kernel pair of an étale morphism to its
target has finite fibres on points if both kernel-pair projections are quasi-compact. -/
theorem kernelPairHom_pointsMap_finite_preimage_singleton (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (ht : AlgebraicGeometry.QuasiCompact (kernelPair φ hφ.rep).t.left)
    (hs : AlgebraicGeometry.QuasiCompact (kernelPair φ hφ.rep).s.left) (x : Points X) :
    (Points.map (kernelPairHom φ hφ) ⁻¹' {x}).Finite :=
  sorry

/-- If an étale morphism from a scheme to an algebraic space is quasi-compact, then the first
projection of the represented kernel pair is quasi-compact. -/
theorem quasiCompact_kernelPair_t (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ) :
    AlgebraicGeometry.QuasiCompact (kernelPair φ hφ.rep).t.left :=
  sorry

/-- If an étale morphism from a scheme to an algebraic space is quasi-compact, then the second
projection of the represented kernel pair is quasi-compact. -/
theorem quasiCompact_kernelPair_s (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ) :
    AlgebraicGeometry.QuasiCompact (kernelPair φ hφ.rep).s.left :=
  sorry

/-- An étale quasi-compact morphism from a scheme to an algebraic space has finite fibres
on points. -/
theorem pointsMap_finite_preimage_singleton_of_quasiCompact (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ)
    (x : Points X) :
    (Points.map φ ⁻¹' {x}).Finite :=
  sorry

/-- The canonical morphism from the represented kernel pair of an étale quasi-compact
morphism to its target has finite fibres on points. -/
theorem kernelPairHom_pointsMap_finite_preimage_singleton_of_quasiCompact (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ)
    (x : Points X) :
    (Points.map (kernelPairHom φ hφ) ⁻¹' {x}).Finite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
