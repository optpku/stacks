/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Cohomology
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded

/-!
# Integral compatibility facade for enriched Hom complexes

The reusable chain-level owner is
`CategoryTheory.CochainComplex.Enriched.Over`, parameterized by a commutative base ring.  This
file preserves the historical integral names and keeps only the controlled strict representative
API that is specific to the old presentation.
@stack 0GWQ
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open ComplexShape HomotopyCategory
open DifferentialGradedCategory
open CategoryTheory.CochainComplex.Enriched.Over
open scoped DifferentialGradedCategory

namespace CategoryTheory.CochainComplex.Enriched

variable {C : Type u} [Category.{v} C]

/-- Compatibility statement for the integral Hom-complex differential comparison. -/
theorem moduleComplexIso_comm [Preadditive C] (K L : CochainComplex C ℤ) :
    ∀ i j, (up ℤ).Rel i j →
      𝟙 ((DifferentialGradedCategory.homComplex K L).X i) ≫
          (CochainComplex.HomComplex.moduleComplex ℤ K L).d i j =
        (DifferentialGradedCategory.homComplex K L).d i j ≫
          𝟙 ((CochainComplex.HomComplex.moduleComplex ℤ K L).X j) := sorry

/-- The historical integral name for the generic explicit-base-ring Hom-complex isomorphism. -/
@[stacks 0A8H "canonical integral DG Hom-complex comparison"]
noncomputable abbrev moduleComplexIso [Preadditive C] (K L : CochainComplex C ℤ) :
    DifferentialGradedCategory.homComplex K L ≅
      CochainComplex.HomComplex.moduleComplex ℤ K L :=
  Over.homComplexIso (R := ℤ) K L

/-- Compatibility formula for the forward integral Hom-complex comparison. -/
@[simp]
theorem moduleComplexIso_hom_f [Preadditive C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplexIso K L).hom.f n = 𝟙 _ := sorry

/-- Compatibility formula for the inverse integral Hom-complex comparison. -/
@[simp]
theorem moduleComplexIso_inv_f [Preadditive C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (moduleComplexIso K L).inv.f n = 𝟙 _ := sorry

/-- The historical integral name for simultaneous Hom-complex pre- and postcomposition. -/
@[stacks 0GWQ "functorial canonical integral DG Hom complex"]
noncomputable abbrev homComplexMap [Preadditive C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂) :
    DifferentialGradedCategory.homComplex K₁ L₁ ⟶
      DifferentialGradedCategory.homComplex K₂ L₂ :=
  Over.homComplexMap (R := ℤ) f g

/-- The integral Hom-complex map preserves identities. -/
@[simp]
theorem homComplexMap_id [Preadditive C] (K L : CochainComplex C ℤ) :
    homComplexMap (𝟙 K) (𝟙 L) = 𝟙 (DifferentialGradedCategory.homComplex K L) := sorry

/-- The integral Hom-complex map preserves composition with source variance reversed. -/
theorem homComplexMap_comp [Preadditive C]
    {K₁ K₂ K₃ L₁ L₂ L₃ : CochainComplex C ℤ}
    (f : K₂ ⟶ K₁) (f' : K₃ ⟶ K₂) (g : L₁ ⟶ L₂) (g' : L₂ ⟶ L₃) :
    homComplexMap (f' ≫ f) (g ≫ g') =
      homComplexMap f g ≫ homComplexMap f' g' := sorry

/-- Compatibility with the standard module-valued Hom-complex map. -/
@[reassoc]
theorem homComplexMap_moduleComplexIso_hom [Preadditive C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂) :
    homComplexMap f g ≫ (moduleComplexIso K₂ L₂).hom =
      (moduleComplexIso K₁ L₁).hom ≫ CochainComplex.HomComplex.map ℤ f g := sorry

/-- Compatibility with generic DG precomposition and postcomposition. -/
@[stacks 0GWQ "canonical cochain Hom-complex map agrees with the generic DG action"]
theorem homComplexMap_eq_precomp_postcomp [Preadditive C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂) :
    homComplexMap f g =
      DifferentialGradedCategory.HomComplex.precomp (ofHom f) ≫
        DifferentialGradedCategory.HomComplex.postcomp (ofHom g) := sorry

/-- Compatibility with generic DG precomposition. -/
@[simp]
theorem homComplexMap_eq_precomp [Preadditive C]
    {K₁ K₂ L : CochainComplex C ℤ} (f : K₂ ⟶ K₁) :
    homComplexMap f (𝟙 L) = DifferentialGradedCategory.HomComplex.precomp (ofHom f) := sorry

/-- Compatibility with generic DG postcomposition. -/
@[simp]
theorem homComplexMap_eq_postcomp [Preadditive C]
    {K L₁ L₂ : CochainComplex C ℤ} (g : L₁ ⟶ L₂) :
    homComplexMap (𝟙 K) g = DifferentialGradedCategory.HomComplex.postcomp (ofHom g) := sorry

/-- The historical integral name for Hom-complex homology comparison. -/
@[stacks 0A8L "canonical integral DG Hom-cohomology comparison"]
noncomputable abbrev moduleHomologyLinearEquiv [Preadditive C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (DifferentialGradedCategory.homComplex K L).homology n ≃ₗ[ℤ]
      (CochainComplex.HomComplex.moduleComplex ℤ K L).homology n :=
  Over.homologyLinearEquiv (R := ℤ) K L n

/-- The historical integral name for cohomology as shifted homotopy Hom. -/
@[stacks 0A8L "enriched Hom cohomology as shifted homotopy Hom"]
noncomputable def homotopyHomLinearEquiv [Preadditive C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (DifferentialGradedCategory.homComplex K L).homology n ≃ₗ[ℤ]
      ShiftedHom ((quotient C (up ℤ)).obj K) ((quotient C (up ℤ)).obj L) n :=
  { toAddEquiv := (moduleHomologyLinearEquiv K L n).toAddEquiv.trans
      ((CochainComplex.HomComplex.Module.homologyHomAddEquiv ℤ K L n).trans
        (CochainComplex.HomComplex.Module.HomologyHom.quotientShiftAddEquiv K L n))
    map_smul' := sorry }

/-- A cohomology class mapped to shifted homotopy Hom through the generic owner. -/
@[stacks 0A8L "enriched Hom cohomology class as shifted homotopy Hom"]
def homotopyHomOfHomology [Preadditive C] (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L).homology n) :
    ShiftedHom ((quotient C (up ℤ)).obj K) ((quotient C (up ℤ)).obj L) n :=
  homotopyHomLinearEquiv K L n x

/-- Source naturality of the historical integral Hom comparison. -/
@[stacks 0A8L "source naturality of enriched Hom cohomology in the homotopy category"]
theorem homotopyHomLinearEquiv_naturality_source [Preadditive C]
    {K₁ K₂ L : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K₁ L).homology n) :
    homotopyHomLinearEquiv K₂ L n
        (HomologicalComplex.homologyMap (homComplexMap f (𝟙 L)) n x) =
      (quotient C (up ℤ)).map f ≫ homotopyHomLinearEquiv K₁ L n x := sorry

/-- Target naturality of the historical integral Hom comparison. -/
@[stacks 0A8L "target naturality of enriched Hom cohomology in the homotopy category"]
theorem homotopyHomLinearEquiv_naturality_target [Preadditive C]
    {K L₁ L₂ : CochainComplex C ℤ} (g : L₁ ⟶ L₂) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L₁).homology n) :
    homotopyHomLinearEquiv K L₂ n
        (HomologicalComplex.homologyMap (homComplexMap (𝟙 K) g) n x) =
      homotopyHomLinearEquiv K L₁ n x ≫ ((quotient C (up ℤ)).map g)⟦n⟧' := sorry

/-- Two-variable naturality of the historical integral Hom comparison. -/
theorem homotopyHomLinearEquiv_naturality [Preadditive C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂)
    (n : ℤ) (x : (DifferentialGradedCategory.homComplex K₁ L₁).homology n) :
    homotopyHomLinearEquiv K₂ L₂ n
        (HomologicalComplex.homologyMap (homComplexMap f g) n x) =
      (quotient C (up ℤ)).map f ≫ homotopyHomLinearEquiv K₁ L₁ n x ≫
        ((quotient C (up ℤ)).map g)⟦n⟧' := sorry

/-- The controlled cycle representative is closed for the standard Hom-complex differential. -/
theorem cycleOfHomology_delta [Preadditive C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L).homology n) :
    CochainComplex.HomComplex.δ n (n + 1)
        (ModuleCat.Hom.hom ((DifferentialGradedCategory.homComplex K L).iCycles n)
          (DifferentialGradedCategory.HomComplex.cycleOfHomology K L n x)) = 0 := sorry

/-- A controlled, noncanonical strict cochain-map representative.  Invariant constructions should
use `homotopyHomOfHomology` instead. -/
@[stacks 0A8L "controlled strict representative of Hom cohomology"]
def chosenHomOfHomology [Preadditive C] (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L).homology n) : K ⟶ L⟦n⟧ :=
  CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (CochainComplex.HomComplex.Cocycle.mk
      (ModuleCat.Hom.hom
        ((DifferentialGradedCategory.homComplex K L).iCycles n)
        (DifferentialGradedCategory.HomComplex.cycleOfHomology K L n x))
      (n + 1) rfl (cycleOfHomology_delta K L n x))

/-- The strict representative has the canonical shifted-homotopy class. -/
@[simp]
theorem chosenHomOfHomology_quotient [Preadditive C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L).homology n) :
    (quotient C (up ℤ)).map (chosenHomOfHomology K L n x) ≫
        ((quotient C (up ℤ)).commShiftIso n).hom.app L =
      homotopyHomOfHomology K L n x := sorry

end CategoryTheory.CochainComplex.Enriched
