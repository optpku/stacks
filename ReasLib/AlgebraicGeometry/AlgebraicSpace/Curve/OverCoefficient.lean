/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField

/-!
# Curve families over coefficient spectra

A proper scheme of topological Krull dimension at most one over a field
induces a family of curves over a coefficient spectrum, with base map
induced by the coefficient algebra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The morphism of algebraic spaces over `Spec Λ` associated to a scheme over
a field, with base `Spec k ⟶ Spec Λ`. -/
def schemeOverCoefficientHom {k : Type u} [Field k] (X : SchemeOverField k)
    (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    ofOver (Over.mk (X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)))) ⟶
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)))) :=
  ofOverHomMk X.hom rfl

/-- `schemeOverCoefficientHom X Λ` is `ofOverHomMk` of the structure morphism
of `X` over the coefficient base. -/
theorem schemeOverCoefficientHom_eq {k : Type u} [Field k]
    (X : SchemeOverField k) (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    schemeOverCoefficientHom X Λ = ofOverHomMk X.hom rfl :=
  rfl

/-- A proper scheme over a field remains fp-flat-proper as a morphism of
algebraic spaces over a coefficient base `Spec Λ`. -/
instance instFpFlatProper_schemeOverCoefficientHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    FpFlatProper (schemeOverCoefficientHom X Λ) :=
  sorry

/-- A proper scheme of topological Krull dimension at most one over a field has
relative dimension at most one over a coefficient base `Spec Λ`. -/
theorem relativeDimensionLE_schemeOverCoefficientHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (Λ : Type u)
    [CommRing Λ] [Algebra Λ k] :
    RelativeDimensionLE (schemeOverCoefficientHom X Λ) 1 :=
  sorry

/-- Package a proper scheme of topological Krull dimension at most one over a
field as a family of curves over `Spec Λ` with base `Spec k ⟶ Spec Λ`. -/
def mkOverCoefficient {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (Λ : Type u) [CommRing Λ] [Algebra Λ k] :
    Obj (Spec (CommRingCat.of Λ)) :=
  @mk (Spec (CommRingCat.of Λ)) (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k))))
    (ofOver (Over.mk (X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ k)))))
    (schemeOverCoefficientHom X Λ)
    (instFpFlatProper_schemeOverCoefficientHom X Λ)
    (relativeDimensionLE_schemeOverCoefficientHom X hdim Λ)

/-- The structure morphism of `mkOverCoefficient X hdim Λ` is
`schemeOverCoefficientHom X Λ`. -/
theorem mkOverCoefficient_hom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (Λ : Type u)
    [CommRing Λ] [Algebra Λ k] :
    hom (mkOverCoefficient X hdim Λ) = schemeOverCoefficientHom X Λ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
