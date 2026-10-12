/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import stacks_project.Chap60.Lemma_60_25_4_AlphaP
public import stacks_project.Chap60.Lemma_60_25_4_Linearization

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

/-- The `i`-th crystalline cohomology group `H^i(Cris(X/S), G)` of an abelian sheaf on
`Cris(X/S)`, realized as Zariski hypercohomology of `Ru_{X/S,*} G`. -/
def crystallineCohomology
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
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
    (G : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u})
    (i : ℕ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).obj
    ((siteAbelianSectionsDerived X.smallZariskiTopology
        ((smallZariskiOpenFunctor X).obj ⊤)).obj
      (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p G))

/-- Unfolding of `crystallineCohomology` as homology of derived Zariski sections of
`Ru_{X/S,*} G`. -/
theorem crystallineCohomology_eq
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
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
    (G : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u})
    (i : ℕ) :
    crystallineCohomology I γ h_compatible s x₀ h_p G i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).obj
        ((siteAbelianSectionsDerived X.smallZariskiTopology
            ((smallZariskiOpenFunctor X).obj ⊤)).obj
          (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p G)) :=
  sorry

variable {X' : Scheme.{u}} (x'₀ : X' ⟶ I.subscheme)
variable (f : X' ⟶ X) (h_over : f ≫ x₀ = x'₀)
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

/-- The pullback `f^*` on crystalline cohomology induced by the unit of
`f_cris^* ⊣ f_cris_*`, as homology of derived Zariski sections of
`linearizationComparison`. -/
def iteratedAlphaPCover_crystallineCohomology_map
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
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
    (i : ℕ) :
    crystallineCohomology I γ h_compatible s x₀ h_p
        ((SheafOfModules.toSheaf _).obj F) i ⟶
      crystallineCohomology I γ h_compatible s x₀ h_p
        ((crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f
            h_over h_p').obj
          (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F)) i :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
    ((siteAbelianSectionsDerived X.smallZariskiTopology
        ((smallZariskiOpenFunctor X).obj ⊤)).map
      (linearizationComparison I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F))

/-- Unfolding of `iteratedAlphaPCover_crystallineCohomology_map` as homology of
`RΓ` applied to `linearizationComparison`. -/
theorem iteratedAlphaPCover_crystallineCohomology_map_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
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
    (i : ℕ) :
    iteratedAlphaPCover_crystallineCohomology_map I γ h_compatible s x₀ h_p x'₀ f
        h_over h_p' F i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i : ℤ)).map
        ((siteAbelianSectionsDerived X.smallZariskiTopology
            ((smallZariskiOpenFunctor X).obj ⊤)).map
          (linearizationComparison I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F)) :=
  sorry

/-- The target of `iteratedAlphaPCover_crystallineCohomology_map` is isomorphic to
`H^i(Cris(X'/S), F')`, i.e. crystalline cohomology of `f_cris^* F` on `X'`. -/
theorem iteratedAlphaPCover_crystallineCohomology_map_target_iso
    [Scheme.IsCharP X p] [Scheme.IsCharP X' p]
    [IsIteratedAlphaPCover p f]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) AddCommGrpCat.{u}]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X' x'₀) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p') AddCommGrpCat.{u}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasSheafify X'.smallZariskiTopology AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X' x'₀ h_p').op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallCrystallineInclusion S I γ h_compatible X' x'₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X' x'₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (relativeCrystallineFunctor I γ h_compatible s x₀ h_p x'₀ f h_over
          h_p').op.HasPointwiseRightKanExtension P]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X' x'₀ h_p')
        AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf X'.smallZariskiTopology AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor X.smallZariskiTopology
          ((smallZariskiOpenFunctor X).obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallZariskiTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived
        (siteAbelianSectionsFunctor X'.smallZariskiTopology
          ((smallZariskiOpenFunctor X').obj ⊤)))
      (HomologicalComplex.quasiIso
        (Sheaf X'.smallZariskiTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p))
    (i : ℕ) :
    IsIsomorphic
      (crystallineCohomology I γ h_compatible s x₀ h_p
        ((crystallineAbelianCrisPushforward I γ h_compatible s x₀ h_p x'₀ f
            h_over h_p').obj
          (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F)) i)
      (crystallineCohomology I γ h_compatible s x'₀ h_p'
        (crystallinePullback I γ h_compatible s x₀ h_p x'₀ f h_over h_p' F) i) :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
