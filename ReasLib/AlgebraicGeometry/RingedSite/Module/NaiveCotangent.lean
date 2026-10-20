/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naive cotangent complexes on a ringed site

This module uses the canonical polynomial presentations owned by `CategoryTheory.Sheaf.FreeAlgebra`
and owns the resulting two-term naive cotangent complexes.  It builds on the independent
conormal-sequence API; all constructions are generic in the site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open ComplexShape
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open scoped ZeroObject TensorProduct

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O₁ O₂ O₃ : Sheaf J CommRingCat.{w}}

namespace Presentation

/-- The terms of the two-term naive cotangent complex associated to a composable presentation. -/
abbrev term (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    ℤ → SheafOfModules (ringSheaf J O₃)
  | Int.negSucc 0 => conormalSource alpha
  | Int.ofNat 0 => conormalTensorTerm phi alpha
  | _ => 0

/-- The differential of the naive cotangent complex associated to a composable presentation. -/
noncomputable def differential
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) (n : ℤ) :
    term phi alpha n ⟶ term phi alpha (n + 1) :=
  match n with
  | Int.negSucc 0 => conormalMap phi alpha
  | _ => 0

/-- The presentationwise naive cotangent differential squares to zero. -/
theorem differential_sq_zero
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) (n : ℤ) :
    differential phi alpha n ≫ differential phi alpha (n + 1) = 0 := sorry

/-- The two-term complex `I / I ^ 2 ⟶ O₃ ⊗[O₂] Ω(O₂/O₁)` associated to a
composable presentation. -/
noncomputable abbrev complex
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CochainComplex (SheafOfModules (ringSheaf J O₃)) ℤ :=
  CochainComplex.of (term phi alpha) (differential phi alpha)
    (differential_sq_zero phi alpha)

/-- The relative-differentials target of a presentationwise naive cotangent complex,
concentrated in degree zero. -/
@[stacks 08TF "conormal augmentation target", stacks 08TS "augmentation target"]
noncomputable abbrev differentialsComplex
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CochainComplex (SheafOfModules (ringSheaf J O₃)) ℤ :=
  (HomologicalComplex.single _ (up ℤ) 0).obj
    (relativeDifferentials (phi ≫ alpha))

/-- The outgoing differential of a presentationwise naive cotangent complex followed by
the conormal-sequence projection is zero. -/
theorem d_comp_conormalToDifferentials
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) (i : ℤ) :
    (complex phi alpha).d i 0 ≫ conormalToDifferentials phi alpha = 0 := sorry

/-- The canonical augmentation from a presentationwise naive cotangent complex to relative
differentials concentrated in degree zero. -/
@[stacks 08TF "conormal augmentation", stacks 08TS "presentation augmentation"]
noncomputable def augmentation
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    complex phi alpha ⟶ differentialsComplex phi alpha :=
  HomologicalComplex.mkHomToSingle (conormalToDifferentials phi alpha)
    (fun i _ ↦ d_comp_conormalToDifferentials phi alpha i)

/-- The degree-zero component of the augmentation is the right map in the conormal sequence. -/
theorem augmentation_f_zero (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    (augmentation phi alpha).f 0 = conormalToDifferentials phi alpha := sorry

/-- The outgoing map in the degree-zero short complex of a presentationwise naive cotangent
complex is zero. -/
theorem degreeZeroSc_g (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    ((complex phi alpha).sc' (-1) 0 1).g = 0 := sorry

/-- The degree-zero homology data obtained by presenting relative differentials as the cokernel
of the conormal map. -/
@[stacks 08TF "conormal cokernel homology data",
  stacks 08TS "conormal cokernel homology data"]
noncomputable def degreeZeroHomologyData
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    ((complex phi alpha).sc' (-1) 0 1).HomologyData :=
  ShortComplex.HomologyData.ofIsColimitCokernelCofork _
    (degreeZeroSc_g phi alpha)
    (CokernelCofork.ofπ (conormalToDifferentials phi alpha)
      (conormal_comp_zero phi alpha))
    (@ShortComplex.Exact.gIsCokernel _ _ _ (conormalSequence phi alpha) _
      (SheafOfModules.RingedSite.conormalSequence_exact phi alpha)
      (SheafOfModules.RingedSite.conormalToDifferentials_epi phi alpha))

/-- Degree-zero homology of the presentationwise naive cotangent complex, computed by the
conormal cokernel universal property. -/
@[stacks 08TF "conormal cokernel homology isomorphism",
  stacks 08TS "conormal cokernel homology isomorphism"]
noncomputable def conormalHomologyIso
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    (complex phi alpha).homology 0 ≅ relativeDifferentials (phi ≫ alpha) :=
  (complex phi alpha).homologyIsoSc' (-1) 0 1
      ((CochainComplex.prev ℤ 0).trans (zero_sub (1 : ℤ)))
      ((CochainComplex.next ℤ 0).trans (zero_add (1 : ℤ))) ≪≫
    (degreeZeroHomologyData phi alpha).left.homologyIso

namespace Augmentation

/-- The explicit inverse of the map induced on degree-zero homology by the presentationwise
augmentation. -/
@[stacks 08TF "augmentation homology inverse", stacks 08TS "augmentation homology inverse"]
noncomputable def homologyMapZeroInv
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    (differentialsComplex phi alpha).homology 0 ⟶
      (complex phi alpha).homology 0 :=
  (HomologicalComplex.singleObjHomologySelfIso (up ℤ) 0
      (relativeDifferentials (phi ≫ alpha))).hom ≫
    (conormalHomologyIso phi alpha).inv

/-- The augmentation homology map followed by its explicit inverse is the identity. -/
@[simp, stacks 08TF "augmentation homology forward-inverse law",
  stacks 08TS "augmentation homology forward-inverse law"]
theorem homologyMap_comp_zeroInv
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    HomologicalComplex.homologyMap (augmentation phi alpha) 0 ≫
      homologyMapZeroInv phi alpha = 𝟙 _ := sorry

/-- The explicit inverse of the augmentation homology map followed by that map is the
identity. -/
@[simp, stacks 08TF "augmentation homology inverse-forward law",
  stacks 08TS "augmentation homology inverse-forward law"]
theorem homologyMapZeroInv_comp
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    homologyMapZeroInv phi alpha ≫
      HomologicalComplex.homologyMap (augmentation phi alpha) 0 = 𝟙 _ := sorry

/-- The literal isomorphism on degree-zero homology induced by the presentationwise
augmentation. -/
@[stacks 08TF "augmentation homology isomorphism",
  stacks 08TS "augmentation homology isomorphism"]
noncomputable def homologyMapZeroIso
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    (complex phi alpha).homology 0 ≅
      (differentialsComplex phi alpha).homology 0 where
  hom := HomologicalComplex.homologyMap (augmentation phi alpha) 0
  inv := homologyMapZeroInv phi alpha
  hom_inv_id := homologyMap_comp_zeroInv phi alpha
  inv_hom_id := homologyMapZeroInv_comp phi alpha

/-- For a locally surjective presentation, the augmentation induces an isomorphism on
degree-zero homology. -/
@[stacks 08TF "degree-zero homology", stacks 08TS "degree-zero homology"]
instance homologyMap_zero_isIso
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    IsIso (HomologicalComplex.homologyMap (augmentation phi alpha) 0) := sorry

end Augmentation

/-- The canonical map from degree-zero homology of a presentationwise naive cotangent complex
to the corresponding sheaf of relative differentials. -/
@[stacks 08TF "degree-zero homology map", stacks 08TS "degree-zero homology map"]
noncomputable def homologyZeroMap
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    (complex phi alpha).homology 0 ⟶ relativeDifferentials (phi ≫ alpha) :=
  HomologicalComplex.homologyMap (augmentation phi alpha) 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (up ℤ) 0
      (relativeDifferentials (phi ≫ alpha))).hom

/-- The named inverse of `homologyZeroMap` for a locally surjective presentation. -/
@[stacks 08TF "degree-zero homology inverse", stacks 08TS "degree-zero homology inverse"]
noncomputable def homologyZeroInv
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    relativeDifferentials (phi ≫ alpha) ⟶ (complex phi alpha).homology 0 :=
  (conormalHomologyIso phi alpha).inv

/-- The degree-zero homology map followed by its named inverse is the identity. -/
@[simp, stacks 08TF "degree-zero homology forward-inverse law",
  stacks 08TS "degree-zero homology forward-inverse law"]
theorem homologyZeroMap_comp_inv
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    homologyZeroMap phi alpha ≫ homologyZeroInv phi alpha = 𝟙 _ := sorry

/-- The named degree-zero homology inverse followed by the forward map is the identity. -/
@[simp, stacks 08TF "degree-zero homology inverse-forward law",
  stacks 08TS "degree-zero homology inverse-forward law"]
theorem homologyZeroInv_comp_map
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    homologyZeroInv phi alpha ≫ homologyZeroMap phi alpha = 𝟙 _ := sorry

/-- The degree-zero homology of a locally surjective presentationwise naive cotangent complex
is canonically the sheaf of relative differentials. -/
@[stacks 08TF "degree-zero homology", stacks 08TS "degree-zero homology"]
noncomputable def homologyZeroIso
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    (complex phi alpha).homology 0 ≅ relativeDifferentials (phi ≫ alpha) where
  hom := homologyZeroMap phi alpha
  inv := homologyZeroInv phi alpha
  hom_inv_id := homologyZeroMap_comp_inv phi alpha
  inv_hom_id := homologyZeroInv_comp_map phi alpha

/-- The forward morphism of the presentationwise degree-zero homology isomorphism is
`homologyZeroMap`. -/
@[simp, stacks 08TF "degree-zero homology isomorphism hom",
  stacks 08TS "degree-zero homology isomorphism hom"]
theorem homologyZeroIso_hom
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    (homologyZeroIso phi alpha).hom = homologyZeroMap phi alpha := sorry

/-- The inverse morphism of the presentationwise degree-zero homology isomorphism is
`homologyZeroInv`. -/
@[simp, stacks 08TF "degree-zero homology isomorphism inv",
  stacks 08TS "degree-zero homology isomorphism inv"]
theorem homologyZeroIso_inv
    (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective alpha] :
    (homologyZeroIso phi alpha).inv = homologyZeroInv phi alpha := sorry

/-- The degree `-1` term of a presentationwise naive cotangent complex is its conormal source. -/
theorem X_negOne (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    (complex phi alpha).X (-1) = conormalSource alpha := sorry

/-- The degree `0` term of a presentationwise naive cotangent complex is its tensor term. -/
theorem X_zero (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    (complex phi alpha).X 0 = conormalTensorTerm phi alpha := sorry

/-- The differential from degree `-1` to degree `0` is the conormal map. -/
theorem d_negOne_zero (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    (complex phi alpha).d (-1) 0 = conormalMap phi alpha := sorry

/-- The conormal map of the canonical polynomial presentation has
cokernel `Ω(B/A)`, equivalently its conormal sequence is exact. -/
@[stacks 08TI "canonical presentation conormal map",
  stacks 08TS "canonical presentation conormal sequence"]
theorem conormalSequence_exact
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (conormalSequence (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B)).Exact := sorry

end Presentation

/-- The naive cotangent complex of
`B` over `A`, built from the canonical polynomial presentation. -/
@[stacks 08TJ, stacks 08TW]
noncomputable abbrev obj
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    CochainComplex (SheafOfModules (ringSheaf J B.right)) ℤ :=
  Presentation.complex (FreeAlgebra.Presentation.base A B)
    (FreeAlgebra.Presentation.map A B)

/-- The relative-differentials target of the canonical naive cotangent complex, concentrated in
degree zero. -/
@[stacks 08TJ "degree-zero target", stacks 08TW "degree-zero target"]
noncomputable abbrev differentialsComplex
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    CochainComplex (SheafOfModules (ringSheaf J B.right)) ℤ :=
  (HomologicalComplex.single _ (up ℤ) 0).obj
    (relativeDifferentials B.hom)

/-- Relative differentials for the composite in the canonical polynomial presentation identify
with relative differentials for the presented algebra map. -/
noncomputable def differentialsIso
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    relativeDifferentials
        (FreeAlgebra.Presentation.base A B ≫ FreeAlgebra.Presentation.map A B) ≅
      relativeDifferentials B.hom :=
  eqToIso (congrArg relativeDifferentials (FreeAlgebra.Presentation.base_map A B))

/-- The canonical augmentation `NL(B/A) ⟶ Ω(B/A)[0]`. -/
@[stacks 08TJ "canonical augmentation", stacks 08TW "canonical augmentation"]
noncomputable def augmentation
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    obj A B ⟶ differentialsComplex A B :=
  Presentation.augmentation (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B) ≫
    (HomologicalComplex.single _ (up ℤ) 0).map (differentialsIso A B).hom

/-- The degree-zero component of the canonical augmentation is the conormal-sequence projection,
followed by the canonical identification with `Ω(B/A)`. -/
theorem augmentation_f_zero
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (augmentation A B).f 0 =
      conormalToDifferentials (FreeAlgebra.Presentation.base A B)
          (FreeAlgebra.Presentation.map A B) ≫
        (differentialsIso A B).hom := sorry

namespace Augmentation

/-- The explicit inverse of the map induced on degree-zero homology by the canonical
augmentation. -/
@[stacks 08TJ "augmentation homology inverse", stacks 08TW "augmentation homology inverse"]
noncomputable def homologyMapZeroInv
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (differentialsComplex A B).homology 0 ⟶ (obj A B).homology 0 :=
  (HomologicalComplex.singleObjHomologySelfIso (up ℤ) 0
      (relativeDifferentials B.hom)).hom ≫
    (differentialsIso A B).inv ≫
    Presentation.homologyZeroInv (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B)

/-- The canonical augmentation homology map followed by its explicit inverse is the identity. -/
@[simp, stacks 08TJ "augmentation homology forward-inverse law",
  stacks 08TW "augmentation homology forward-inverse law"]
theorem homologyMap_comp_zeroInv
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    HomologicalComplex.homologyMap (augmentation A B) 0 ≫
      homologyMapZeroInv A B = 𝟙 _ := sorry

/-- The explicit inverse of the canonical augmentation homology map followed by that map is the
identity. -/
@[simp, stacks 08TJ "augmentation homology inverse-forward law",
  stacks 08TW "augmentation homology inverse-forward law"]
theorem homologyMapZeroInv_comp
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    homologyMapZeroInv A B ≫
      HomologicalComplex.homologyMap (augmentation A B) 0 = 𝟙 _ := sorry

/-- The literal isomorphism on degree-zero homology induced by the canonical augmentation. -/
@[stacks 08TJ "augmentation homology isomorphism",
  stacks 08TW "augmentation homology isomorphism"]
noncomputable def homologyMapZeroIso
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (obj A B).homology 0 ≅ (differentialsComplex A B).homology 0 where
  hom := HomologicalComplex.homologyMap (augmentation A B) 0
  inv := homologyMapZeroInv A B
  hom_inv_id := homologyMap_comp_zeroInv A B
  inv_hom_id := homologyMapZeroInv_comp A B

/-- The canonical augmentation induces an isomorphism on degree-zero homology. -/
@[stacks 08TJ "degree-zero homology", stacks 08TW "degree-zero homology"]
instance homologyMap_zero_isIso
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    IsIso (HomologicalComplex.homologyMap (augmentation A B) 0) := sorry

end Augmentation

/-- The canonical degree-zero homology map, obtained from the presentationwise map through the
canonical identification of relative differentials. -/
@[stacks 08TJ "degree-zero homology map", stacks 08TW "degree-zero homology map"]
noncomputable def homologyZeroMap
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (obj A B).homology 0 ⟶ relativeDifferentials B.hom :=
  Presentation.homologyZeroMap (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B) ≫
    (differentialsIso A B).hom

/-- The named inverse of the canonical degree-zero homology map. -/
@[stacks 08TJ "degree-zero homology inverse", stacks 08TW "degree-zero homology inverse"]
noncomputable def homologyZeroInv
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    relativeDifferentials B.hom ⟶ (obj A B).homology 0 :=
  (differentialsIso A B).inv ≫
    Presentation.homologyZeroInv (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B)

/-- The canonical degree-zero homology map agrees with the map induced by the canonical
augmentation, followed by the homology identification for a complex concentrated in degree zero. -/
@[stacks 08TJ "canonical augmentation homology map",
  stacks 08TW "canonical augmentation homology map"]
theorem homologyZeroMap_eq_augmentation
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    homologyZeroMap A B =
      HomologicalComplex.homologyMap (augmentation A B) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (up ℤ) 0
          (relativeDifferentials B.hom)).hom := sorry

/-- The canonical degree-zero homology map followed by its named inverse is the identity. -/
@[simp, stacks 08TJ "degree-zero homology forward-inverse law",
  stacks 08TW "degree-zero homology forward-inverse law"]
theorem homologyZeroMap_comp_inv
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    homologyZeroMap A B ≫ homologyZeroInv A B = 𝟙 _ := sorry

/-- The named canonical degree-zero homology inverse followed by the forward map is the identity. -/
@[simp, stacks 08TJ "degree-zero homology inverse-forward law",
  stacks 08TW "degree-zero homology inverse-forward law"]
theorem homologyZeroInv_comp_map
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    homologyZeroInv A B ≫ homologyZeroMap A B = 𝟙 _ := sorry

/-- The degree-zero homology of the canonical naive cotangent complex is canonically
`Ω(B/A)`. -/
@[stacks 08TJ "degree-zero homology", stacks 08TW "degree-zero homology"]
noncomputable def homologyZeroIso
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (obj A B).homology 0 ≅ relativeDifferentials B.hom where
  hom := homologyZeroMap A B
  inv := homologyZeroInv A B
  hom_inv_id := homologyZeroMap_comp_inv A B
  inv_hom_id := homologyZeroInv_comp_map A B

/-- The forward morphism of the canonical degree-zero homology isomorphism is
`homologyZeroMap`. -/
@[simp, stacks 08TJ "degree-zero homology isomorphism hom",
  stacks 08TW "degree-zero homology isomorphism hom"]
theorem homologyZeroIso_hom
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (homologyZeroIso A B).hom = homologyZeroMap A B := sorry

/-- The inverse morphism of the canonical degree-zero homology isomorphism is
`homologyZeroInv`. -/
@[simp, stacks 08TJ "degree-zero homology isomorphism inv",
  stacks 08TW "degree-zero homology isomorphism inv"]
theorem homologyZeroIso_inv
    (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (homologyZeroIso A B).inv = homologyZeroInv A B := sorry

/-- The degree `-1` term of the canonical naive cotangent complex is its conormal source. -/
theorem X_negOne (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (obj A B).X (-1) = conormalSource (FreeAlgebra.Presentation.map A B) := sorry

/-- The degree `0` term of the canonical naive cotangent complex is its cotangent tensor term. -/
theorem X_zero (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (obj A B).X 0 = conormalTensorTerm (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B) := sorry

/-- The only nonzero differential of the canonical naive cotangent complex is its conormal map. -/
@[stacks 08TV]
theorem d_negOne_zero (A : Sheaf J CommRingCat.{w}) (B : Under A) :
    (obj A B).d (-1) 0 = conormalMap (FreeAlgebra.Presentation.base A B)
      (FreeAlgebra.Presentation.map A B) := sorry

end SheafOfModules.RingedSite.NaiveCotangent

-- The degree-zero inverse data is obtained from the conormal cokernel universal property and then
-- transported through the concentrated-degree-zero comparison.  The `IsIso` declarations remain
-- Prop-level interfaces; they do not own or select the inverse morphisms.  Any `sorryAx` in the
-- data owners is inherited through square-zero, exactness, epi, and universal-property laws.
