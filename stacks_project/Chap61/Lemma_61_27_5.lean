module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Derived.ConstructibleTensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
  CategoryTheory.Sheaf
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u w

-- Local declaration justification (instance diamond): Sheaf is a FullSubcategory, whose
-- inherited HasZeroMorphisms/Preadditive instances conflict with the Abelian-induced
-- structures used by DerivedCategory.Q; the complete expected type, including its
-- prerequisite binders and tensor conclusion, must elaborate under the same suppression.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory
  Preadditive.fullSubcategory in

/- Lemma 61.27.5: for a scheme `X` and a Noetherian ring `Λ`, if `K` and `L` lie in
`D_c^-(X.ProEt, Λ)`, then the derived tensor product `K ⊗ᴸ L` again lies in
`D_c^-(X.ProEt, Λ)`. -/
@[stacks 09BQ] #check
  (AlgebraicGeometry.Scheme.constructibleProEtaleModule_derivedTensor :
    ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
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
    (hL_c : DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) L),
    DerivedCategory.IsBoundedAbove (K ⊗ᴸ L) ∧
      DerivedCategory.cohomologyIn (constructibleProEtaleModule X Λ) (K ⊗ᴸ L))

end
