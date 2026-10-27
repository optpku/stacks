/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality.Abelian
public import ReasLib.CategoryTheory.Sites.Derived.Sections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Crystalline
open CategoryTheory.Functor.RightDerived
open SheafOfModules

noncomputable section

universe u v dC dZ

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

/-- The degree-`i` crystalline cohomology of an abelian sheaf is the homology of derived
Zariski global sections of its derived crystalline direct image. The coefficient universe and
the chosen crystalline and Zariski derived-category models are independent. -/
def crystallineCohomology
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v}]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{v}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{v},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasDerivedCategory.{dC}
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    [HasDerivedCategory.{dZ} (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{v})]
    [IsGrothendieckAbelian (Sheaf X.smallZariskiTopology AddCommGrpCat.{v})]
    (G : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{v}) (i : ℕ) : AddCommGrpCat.{v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v} (i : ℤ)).obj
    ((siteAbelianSectionsDerivedWith X.smallZariskiTopology
        ((smallZariskiOpenFunctor X).obj ⊤) :
          DerivedCategory.{dZ} (Sheaf X.smallZariskiTopology AddCommGrpCat.{v}) ⥤
            DerivedCategory AddCommGrpCat.{v}).obj
      (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p G))

variable {X' : Scheme.{u}} (x'₀ : X' ⟶ I.subscheme)
variable (f : X' ⟶ X) (h_over : f ≫ x₀ = x'₀)
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

/-- The comparison on crystalline cohomology induced by the abelian inverse-image
adjunction, computed by applying derived Zariski sections to its derived direct-image unit.
Its coefficients use abelian inverse image rather than extension of scalars for modules. -/
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

end AlgebraicGeometry.Scheme.Crystalline
