module

public import stacks_project.Chap63.Lemma_63_5_3
public import stacks_project.Chap63.Lemma_63_5_4_Comparison

/-!
# Composition of derived weighting traces

Lemma 63.5.4: for composable locally quasi-finite morphisms, derived
weighting traces compose after the identification
`(g ∘ f)_! (g ∘ f)⁻¹ K ≅ g_! f_! f⁻¹ g⁻¹ K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (f ≫ g)).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (f ≫ g)).op]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- `weightingTraceDerived` of `f ≫ g` with an explicit weighting function. -/
abbrev weightingTraceDerived_ofWeight (w : X → ℤ) (hw : (f ≫ g).IsWeighting w)
    (K : EtaleDerived Z Λ) :
    (lowerShriekModuleDerived (f ≫ g) Λ).obj
        ((etaleModuleDerivedInverseImage (f ≫ g) Λ).obj K) ⟶ K :=
  weightingTraceDerived (f ≫ g) Λ hw K

/-- `weightingTraceDerived_ofWeight` is `weightingTraceDerived` of `f ≫ g`. -/
theorem weightingTraceDerived_ofWeight_eq (w : X → ℤ)
    (hw : (f ≫ g).IsWeighting w) (K : EtaleDerived Z Λ) :
    weightingTraceDerived_ofWeight f g Λ w hw K =
      weightingTraceDerived (f ≫ g) Λ hw K :=
  sorry

/-- Lemma 63.5.4: Let `f : X ⟶ Y` and `g : Y ⟶ Z` be locally quasi-finite.
Let `w_f` be a weighting of `f` and `w_g` a weighting of `g`. For `K` in
`D(Z_étale, Λ)`, the composition
`g_! (Tr_{f, w_f, g⁻¹ K}) ≫ Tr_{g, w_g, K}` equals
`Tr_{f ≫ g, w_{f ≫ g}, K}` after `weightingTraceDerivedCompIso`, where
`w_{f ≫ g}(x) = w_f(x) * w_g(f x)` is `IsWeighting.comp hw_f hw_g`. -/
@[stacks 0GL3]
theorem weightingTraceDerived_comp {w_f : X → ℤ} (hw_f : f.IsWeighting w_f)
    {w_g : Y → ℤ} (hw_g : g.IsWeighting w_g) (K : EtaleDerived Z Λ) :
    (weightingTraceDerivedCompIso f g Λ K).hom ≫
      (lowerShriekModuleDerived g Λ).map
        (weightingTraceDerived f Λ hw_f
          ((etaleModuleDerivedInverseImage g Λ).obj K)) ≫
      weightingTraceDerived g Λ hw_g K =
      weightingTraceDerived_ofWeight f g Λ (fun x ↦ w_f x * w_g (f x))
        (IsWeighting.comp hw_f hw_g) K :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
