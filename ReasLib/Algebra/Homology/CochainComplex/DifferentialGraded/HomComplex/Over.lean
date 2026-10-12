/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Comparison

/-!
# Enriched Hom complexes over an explicit base ring

This leaf connects the explicit differential graded enrichment
`CochainComplex.differentialGradedCategory C R` with the canonical `ModuleCat R`-valued Hom
complex.  It is deliberately independent of homotopy localization and derived functors, so
chain-level consumers can import it directly.
@stack 0GWQ
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace CategoryTheory.CochainComplex.Enriched.Over

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The Hom complex of the explicit `R`-linear differential graded enrichment of cochain
complexes. -/
@[stacks 0A8H "cochain Hom complex over an explicit linear base ring"]
noncomputable abbrev homComplex (X Y : CochainComplex C ℤ) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  @DifferentialGradedCategory.homComplex R _ _
    (CochainComplex.differentialGradedCategory C R) X Y

/-- The explicit differential graded Hom complex is the canonical module-valued Hom complex. -/
@[stacks 0A8H "explicit DG and module-valued cochain Hom complexes"]
noncomputable def homComplexIso (X Y : CochainComplex C ℤ) :
    homComplex (R := R) X Y ≅ CochainComplex.HomComplex.moduleComplex R X Y :=
  Iso.refl _

/-- Simultaneous precomposition and postcomposition on explicit-base-ring Hom complexes. -/
@[stacks 0GWQ "functoriality of explicit-base-ring cochain Hom complexes"]
noncomputable abbrev homComplexMap
    {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ} (f : X₂ ⟶ X₁) (g : Y₁ ⟶ Y₂) :
    homComplex (R := R) X₁ Y₁ ⟶ homComplex (R := R) X₂ Y₂ :=
  CochainComplex.HomComplex.map R f g

/-- Homology of the explicit Hom complex is canonically the homology of the standard module-valued
Hom complex. -/
@[stacks 0A8L "explicit-base-ring Hom-complex homology comparison"]
noncomputable def homologyLinearEquiv (X Y : CochainComplex C ℤ) (n : ℤ) :
    (homComplex (R := R) X Y).homology n ≃ₗ[R]
      (CochainComplex.HomComplex.moduleComplex R X Y).homology n :=
  (HomologicalComplex.homologyMapIso (homComplexIso (R := R) X Y) n).toLinearEquiv

/-- Cohomology of the explicit `R`-linear Hom complex is shifted Hom in the ordinary homotopy
category. -/
@[stacks 0A8L "explicit-base-ring Hom cohomology as shifted homotopy Hom"]
noncomputable def homotopyHomLinearEquiv (X Y : CochainComplex C ℤ) (n : ℤ) :
    (homComplex (R := R) X Y).homology n ≃ₗ[R]
      ShiftedHom ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X)
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y) n :=
  CochainComplex.HomComplex.Module.HomologyHom.linearEquiv R X Y n

/-- A cohomology class in the explicit `R`-linear Hom complex determines its canonical shifted
morphism in the ordinary homotopy category. -/
@[stacks 0A8L "explicit-base-ring Hom cohomology class as shifted homotopy Hom"]
def homotopyHomOfHomology (X Y : CochainComplex C ℤ) (n : ℤ)
    (x : (homComplex (R := R) X Y).homology n) :
    ShiftedHom ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X)
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y) n :=
  homotopyHomLinearEquiv X Y n x

/-- The explicit-base-ring Hom-cohomology comparison is natural in both complexes. -/
@[stacks 0A8L "naturality of explicit-base-ring Hom cohomology"]
theorem homotopyHomLinearEquiv_naturality
    {X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ} (f : X₂ ⟶ X₁) (g : Y₁ ⟶ Y₂)
    (n : ℤ) (x : (homComplex (R := R) X₁ Y₁).homology n) :
    homotopyHomLinearEquiv X₂ Y₂ n
        (HomologicalComplex.homologyMap (homComplexMap f g) n x) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f ≫
        homotopyHomLinearEquiv X₁ Y₁ n x ≫
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g)⟦n⟧' := sorry

end CategoryTheory.CochainComplex.Enriched.Over
