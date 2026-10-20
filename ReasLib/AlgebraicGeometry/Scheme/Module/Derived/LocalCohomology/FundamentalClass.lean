module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.FundamentalClass.Presentation

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.LocalCohomology

variable {X Z : Scheme.{u}}

/-- The additive-presheaf map obtained by extending the chart maps from their genuine
topological basis. -/
noncomputable def extendedMapPresheaf (i : Z ⟶ X) (c : ℕ) (ℱ : Scheme.QCoh X)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    ((sourceFunctor i c).obj ℱ).val.presheaf ⟶ ((functor i c).obj ℱ).val.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom
    ((sourceFunctor i c).obj ℱ).val.presheaf
    ⟨((functor i c).obj ℱ).val.presheaf, ((functor i c).obj ℱ).isSheaf⟩
    (presentations_isBasis i c) (localMap i c ℱ)

/-- The basis extension of the local class maps is linear over the structure sheaf. -/
theorem extendedMapPresheaf_isLinear (i : Z ⟶ X) (c : ℕ) (ℱ : Scheme.QCoh X)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    SheafOfModules.IsLinearOnBasis ((sourceFunctor i c).obj ℱ) ((functor i c).obj ℱ)
      (Set.range (Presentation.carrier (i := i) (c := c)))
      (extendedMapPresheaf i c ℱ) := sorry

/-- The fundamental-class morphism on one quasicoherent coefficient module. -/
noncomputable def fundamentalClassApp (i : Z ⟶ X) (c : ℕ) (ℱ : Scheme.QCoh X)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    (sourceFunctor i c).obj ℱ ⟶ (functor i c).obj ℱ :=
  SheafOfModules.homOfLinearOnBasis ((sourceFunctor i c).obj ℱ) ((functor i c).obj ℱ)
    (extendedMapPresheaf i c ℱ) (presentations_isBasis i c)
    (extendedMapPresheaf_isLinear i c ℱ)

/-- Naturality of the geometrically glued fundamental-class components. -/
theorem fundamentalClassApp_naturality (i : Z ⟶ X) (c : ℕ)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    {ℱ 𝒢 : Scheme.QCoh X} (φ : ℱ ⟶ 𝒢) :
    (sourceFunctor i c).map φ ≫ fundamentalClassApp i c 𝒢 =
      fundamentalClassApp i c ℱ ≫ (functor i c).map φ := sorry

/-- The canonical fundamental-class natural transformation for a finitely presented closed
immersion whose conormal sheaf is finite locally free of rank `c`. -/
noncomputable def fundamentalClass (i : Z ⟶ X) (c : ℕ) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    sourceFunctor i c ⟶ functor i c where
  app ℱ := fundamentalClassApp i c ℱ
  naturality _ _ φ := fundamentalClassApp_naturality i c φ

/-- A component of `fundamentalClass` is the morphism glued from its equation and off-support
chart maps. -/
theorem fundamentalClass_app (i : Z ⟶ X) (c : ℕ) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (ℱ : Scheme.QCoh X) :
    (fundamentalClass i c).app ℱ = fundamentalClassApp i c ℱ := sorry

/-- The fundamental-class components commute with morphisms of quasicoherent modules. -/
theorem fundamentalClass_naturality (i : Z ⟶ X) (c : ℕ)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    {ℱ 𝒢 : Scheme.QCoh X} (φ : ℱ ⟶ 𝒢) :
    (sourceFunctor i c).map φ ≫ (fundamentalClass i c).app 𝒢 =
      (fundamentalClass i c).app ℱ ≫ (functor i c).map φ := sorry

/-- On a genuine equation presentation, `fundamentalClass` is the transported
quotient-descended `ModuleCech.LocalCohomology.quotientClassMap`; change of generators is
governed by `ModuleCech.LocalCohomology.classMap_mulVec`. -/
theorem fundamentalClass_ofPresentation (i : Z ⟶ X) (c : ℕ)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (ℱ : Scheme.QCoh X) (P : EquationPresentation i c) :
    ((fundamentalClass i c).app ℱ).app P.carrier =
      EquationPresentation.sourceComparison P ℱ ≫
        (forget₂ _ _).map
          (((ModuleCech.LocalCohomology.quotientClassMap P.generators).app
            (P.coefficients ℱ)).val.app (op ⊤)) ≫
        EquationPresentation.targetComparison P ℱ := sorry

end AlgebraicGeometry.Scheme.Hom.LocalCohomology

end
