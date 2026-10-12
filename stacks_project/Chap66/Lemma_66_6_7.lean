/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair
public import stacks_project.Chap66.Definition_66_4_1_Points

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

/-- The morphism `ofOver (U ×_X U) ⟶ X` induced by an étale morphism `φ` from a scheme, as
the composite of the first kernel-pair projection with `φ`. -/
def kernelPairHom (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    ofOver (kernelPair φ hφ.rep).left ⟶ X :=
  ofOverMap (kernelPair φ hφ.rep).t ≫ φ

/-- `kernelPairHom φ hφ` is the composite of the first kernel-pair projection with `φ`. -/
theorem kernelPairHom_eq (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    kernelPairHom φ hφ = ofOverMap (kernelPair φ hφ.rep).t ≫ φ :=
  sorry

/-- The two kernel-pair projections become equal after composition with `φ`. -/
theorem kernelPairHom_eq_snd (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    kernelPairHom φ hφ = ofOverMap (kernelPair φ hφ.rep).s ≫ φ :=
  sorry

/-- Lemma 66.6.7 (1): let `S` be a scheme, `X` an algebraic space over `S`, and `U` a scheme.
If `φ : U ⟶ X` is étale and the projections `R = U ×_X U ⟶ U` are quasi-compact, then the
fibres of `|U| ⟶ |X|` are finite. -/
@[stacks 03IJ]
theorem pointsMap_finite_preimage_singleton (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (ht : QuasiCompact (kernelPair φ hφ.rep).t.left)
    (hs : QuasiCompact (kernelPair φ hφ.rep).s.left) (x : Points X) :
    (Points.map φ ⁻¹' {x}).Finite :=
  sorry

/-- Lemma 66.6.7 (2): let `S` be a scheme, `X` an algebraic space over `S`, and `U` a scheme.
If `φ : U ⟶ X` is étale and the projections `R = U ×_X U ⟶ U` are quasi-compact, then the
fibres of `|R| ⟶ |X|` are finite. -/
@[stacks 03IJ]
theorem kernelPairHom_pointsMap_finite_preimage_singleton (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (ht : QuasiCompact (kernelPair φ hφ.rep).t.left)
    (hs : QuasiCompact (kernelPair φ hφ.rep).s.left) (x : Points X) :
    (Points.map (kernelPairHom φ hφ) ⁻¹' {x}).Finite :=
  sorry

/-- If an étale morphism from a scheme to an algebraic space is quasi-compact, then the first
projection of the represented kernel pair is quasi-compact. -/
theorem quasiCompact_kernelPair_t (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ) :
    QuasiCompact (kernelPair φ hφ.rep).t.left :=
  sorry

/-- If an étale morphism from a scheme to an algebraic space is quasi-compact, then the second
projection of the represented kernel pair is quasi-compact. -/
theorem quasiCompact_kernelPair_s (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ) :
    QuasiCompact (kernelPair φ hφ.rep).s.left :=
  sorry

/-- If `φ` is étale and quasi-compact, then the fibres of `|U| ⟶ |X|` are finite. -/
theorem pointsMap_finite_preimage_singleton_of_quasiCompact (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ)
    (x : Points X) :
    (Points.map φ ⁻¹' {x}).Finite :=
  sorry

/-- If `φ` is étale and quasi-compact, then the fibres of `|R| ⟶ |X|` are finite. -/
theorem kernelPairHom_pointsMap_finite_preimage_singleton_of_quasiCompact (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ)
    (hqc : (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact)).presheaf φ)
    (x : Points X) :
    (Points.map (kernelPairHom φ hφ) ⁻¹' {x}).Finite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
