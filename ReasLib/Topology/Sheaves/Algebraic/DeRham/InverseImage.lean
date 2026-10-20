module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.InverseImage
public import ReasLib.Topology.Sheaves.Algebraic.DeRham

/-!
# Inverse image of relative de Rham complexes on topological spaces

This file is the source-facing specialization of the arbitrary-site comparison.  Its morphism is
the same explicit map built from the inverse-image unit, module sheafification, and module
pullback adjunctions.  The inverse-side API of the generic owner requires representable
flatness, which `Opens.map f` has by a mathlib instance.
-/

@[expose] public section

open CategoryTheory ComplexShape TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.DeRham.InverseImage

variable {X Y : TopCat.{u}} (f : Y ⟶ X)
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The morphism of inverse-image commutative ring sheaves induced by `φ`. -/
abbrev ringMap (φ : O₁ ⟶ O₂) :
    (TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₁ ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} f).obj O₂ :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f).map φ

/-- The degree-`p` component of the inverse-image comparison for relative de Rham complexes. -/
@[stacks 0FKP "degreewise comparison on topological spaces"]
noncomputable abbrev comparisonApp (φ : O₁ ⟶ O₂) (p : ℕ) :=
  SheafOfModules.RingedSite.DeRham.comparisonApp
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ p

/-- The named inverse of the degree-`p` topological inverse-image comparison. -/
@[stacks 0FKP "degreewise inverse comparison on topological spaces"]
noncomputable abbrev comparisonAppInv (φ : O₁ ⟶ O₂) (p : ℕ) :
    term (ringMap f φ) p ⟶
      (SheafOfModules.RingedSite.InverseImage.modulePullback
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) O₁).obj (term φ p) :=
  SheafOfModules.RingedSite.DeRham.comparisonAppInv
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ p

/-- The degree-`p` inverse-image comparison as an isomorphism. -/
@[stacks 0FKP "degreewise comparison isomorphism on topological spaces"]
noncomputable abbrev comparisonAppIso (φ : O₁ ⟶ O₂) (p : ℕ) :
    (SheafOfModules.RingedSite.InverseImage.modulePullback
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) O₁).obj (term φ p) ≅ term (ringMap f φ) p :=
  SheafOfModules.RingedSite.DeRham.comparisonAppIso
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ p

/-- The inverse of the degreewise topological comparison is its named generic specialization. -/
@[simp, stacks 0FKP "degreewise comparison isomorphism inverse on topological spaces"]
theorem comparisonAppIso_inv (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparisonAppIso f φ p).inv = comparisonAppInv f φ p := sorry

/-- Lemma 17.30.2 (0FKP): the canonical comparison from the inverse image of the relative de Rham
complex to the relative de Rham complex of the inverse-image ring map. -/
@[stacks 0FKP "comparison on topological spaces"]
noncomputable abbrev comparison (φ : O₁ ⟶ O₂) :
    ((SheafOfModules.RingedSite.InverseImage.modulePullback
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) ⟶
        complex (ringMap f φ) :=
  SheafOfModules.RingedSite.DeRham.comparison
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The named inverse of the topological relative de Rham comparison. -/
@[stacks 0FKP "inverse comparison on topological spaces"]
noncomputable abbrev comparisonInv (φ : O₁ ⟶ O₂) :
    complex (ringMap f φ) ⟶
      ((SheafOfModules.RingedSite.InverseImage.modulePullback
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) :=
  SheafOfModules.RingedSite.DeRham.comparisonInv
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The degree-`p` component of the topological inverse-image comparison is `comparisonApp`. -/
theorem comparison_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparison f φ).f p = comparisonApp f φ p := sorry

/-- The topological inverse-image comparison is canonically an isomorphism. -/
@[stacks 0FKP "topological comparison is an isomorphism"]
theorem comparison_isIso (φ : O₁ ⟶ O₂) :
    IsIso (comparison f φ) := sorry

/-- Lemma 17.30.2 (0FKP): the canonical inverse-image identification of relative de Rham
complexes on topological spaces. -/
@[stacks 0FKP]
noncomputable abbrev iso (φ : O₁ ⟶ O₂) :
    ((SheafOfModules.RingedSite.InverseImage.modulePullback
      (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
      (Opens.map f) O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) ≅
        complex (ringMap f φ) :=
  SheafOfModules.RingedSite.DeRham.comparisonIso
    (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
    (Opens.map f) φ

/-- The forward map of the topological comparison isomorphism is `comparison`. -/
@[simp, stacks 0FKP "topological comparison isomorphism hom"]
theorem iso_hom (φ : O₁ ⟶ O₂) :
    (iso f φ).hom = comparison f φ := sorry

/-- The inverse map of the topological comparison isomorphism is `comparisonInv`. -/
@[simp, stacks 0FKP "topological comparison isomorphism inverse"]
theorem iso_inv (φ : O₁ ⟶ O₂) :
    (iso f φ).inv = comparisonInv f φ := sorry

/-- The degree-`p` forward component of the topological comparison isomorphism is
`comparisonApp`. -/
theorem iso_hom_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (iso f φ).hom.f p = comparisonApp f φ p := sorry

/-- The degree-`p` inverse component of the topological comparison is the inverse of the
degreewise comparison. -/
@[simp, stacks 0FKP "topological inverse comparison component"]
theorem iso_inv_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (iso f φ).inv.f p = comparisonAppInv f φ p := sorry

/-- Inverse image along a continuous map preserves the relative de Rham complex. -/
theorem inverseImage_isIsomorphic (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((SheafOfModules.RingedSite.InverseImage.modulePullback
        (J := Opens.grothendieckTopology X) (K := Opens.grothendieckTopology Y)
        (Opens.map f) O₁).mapHomologicalComplex (up ℕ)).obj (complex φ))
      (complex (ringMap f φ)) := sorry

end TopCat.Sheaf.DeRham.InverseImage
