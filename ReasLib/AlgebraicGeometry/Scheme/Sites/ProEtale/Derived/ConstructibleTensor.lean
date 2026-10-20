module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTensor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.ProEtaleComparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
For a Noetherian coefficient ring, the derived tensor product of bounded-above
complexes with constructible cohomology on the pro-étale site has constructible
cohomology and is bounded above.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
  CategoryTheory.Sheaf
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme

-- Local declaration justification (instance diamond): Sheaf is a FullSubcategory, whose
-- inherited HasZeroMorphisms/Preadditive instances conflict with the Abelian-induced
-- structures used by DerivedCategory.Q; suppression must cover prerequisite binder
-- elaboration as well as the tensor conclusion.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory in
/-- The derived tensor product of bounded-above constructible complexes of
`Λ`-modules on a scheme's pro-étale site is bounded above and constructible. -/
theorem constructibleProEtaleModule_derivedTensor
    {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify (ProEt.topology Y) (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.ProEt),
      HasWeakSheafify ((ProEt.topology Y).over U) (ModuleCat.{w} Λ)]
    [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
      (ProEt.baseChange f).op.HasLeftKanExtension P]
    [Abelian (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
    [(((ProEt.topology X).W : MorphismProperty (X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]
    [MonoidalPreadditive (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))]
    [∀ (K L : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))) (ComplexShape.up ℤ)]
    [h_derivedTensor :
      @DerivedTensor.Right.Has (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) _ _ _ _ _ _]
    (K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)))
    (hK : DerivedCategory.IsBoundedAbove K) (hL : DerivedCategory.IsBoundedAbove L)
    (hK_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) K)
    (hL_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) L) :
    DerivedCategory.IsBoundedAbove (K ⊗ᴸ L) ∧
      DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) (K ⊗ᴸ L) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
