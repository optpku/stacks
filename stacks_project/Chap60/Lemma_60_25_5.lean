module

public import Mathlib.Algebra.Category.Grp.Abelian
public import stacks_project.Chap60.Definition_60_11_3_Crystal
public import stacks_project.Chap60.Lemma_60_25_4_AlphaP
public import stacks_project.Chap60.Lemma_60_25_5_Cohomology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Crystalline
open CategoryTheory.Functor.RightDerived
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable {X' : Scheme.{u}} (x'₀ : X' ⟶ I.subscheme)
variable (f : X' ⟶ X)
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

/-- Lemma 60.25.5 (1): with notations and assumptions as in Lemma 60.25.4, the kernel of
`f^* : H^i(Cris(X/S), F) ⟶ H^i(Cris(X'/S), F')` is annihilated by `q^(i+1)`. -/
@[stacks 07QA]
theorem iteratedAlphaPCover_crystallineCohomology_kernel_nsmul
    (q : ℕ)
    (h_p_mem : ∀ V : S.affineOpens, (p : Γ(S, V)) ∈ I.ideal V)
    (h_over : f ≫ x₀ = x'₀)
    [Scheme.IsCharP X p] [Scheme.IsCharP X' p]
    [IsIteratedAlphaPCover p f] [IsFiniteLocallyFreeOfRank f q]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [(smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
      HasWeakSheafify
        ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U)
        AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
      ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor X.smallZariskiTopology
          ((smallZariskiOpenFunctor X).obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallZariskiTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p))
    [IsCrystalInQuasiCoherentModules F]
    (i : ℕ) :
    (q ^ (i + 1) : ℤ) • 𝟙
      (kernel
        (iteratedAlphaPCover_crystallineCohomology_map I γ h_compatible s x₀ h_p
          x'₀ f h_over h_p' F i)) = 0 :=
  sorry

/-- Lemma 60.25.5 (2): with notations and assumptions as in Lemma 60.25.4, the cokernel of
`f^* : H^i(Cris(X/S), F) ⟶ H^i(Cris(X'/S), F')` is annihilated by `q^(i+1)`. -/
@[stacks 07QA]
theorem iteratedAlphaPCover_crystallineCohomology_cokernel_nsmul
    (q : ℕ)
    (h_p_mem : ∀ V : S.affineOpens, (p : Γ(S, V)) ∈ I.ideal V)
    (h_over : f ≫ x₀ = x'₀)
    [Scheme.IsCharP X p] [Scheme.IsCharP X' p]
    [IsIteratedAlphaPCover p f] [IsFiniteLocallyFreeOfRank f q]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [(smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
      HasWeakSheafify
        ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U)
        AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
      ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor X.smallZariskiTopology
          ((smallZariskiOpenFunctor X).obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallZariskiTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p))
    [IsCrystalInQuasiCoherentModules F]
    (i : ℕ) :
    (q ^ (i + 1) : ℤ) • 𝟙
      (cokernel
        (iteratedAlphaPCover_crystallineCohomology_map I γ h_compatible s x₀ h_p
          x'₀ f h_over h_p' F i)) = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
