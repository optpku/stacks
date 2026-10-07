module

public import stacks_project.Chap63.Lemma_63_4_12
public import stacks_project.Chap63.Lemma_63_5_3_Trace

/-!
# Comparison isomorphism for composite weighting traces

The source identification `(g ∘ f)_! (g ∘ f)⁻¹ K = g_! f_! f⁻¹ g⁻¹ K` is
realized as a composite of `etaleModuleSheafPullback_comp` with a module lift
of `lowerShriekFunctorCompIso`, then passed to derived categories. This does
not use separatedness.
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

/-- Forgetting coefficients identifies `(f ≫ g)_! F` with `g_! (f_! (forget F))`
via `lowerShriekFunctorCompIso`. -/
def weightingTraceModuleLowerShriekCompForgetIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule (f ≫ g) Λ).obj F) ≅
      (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F)) :=
  lowerShriekModule_forget (f ≫ g) Λ F ≪≫
    (lowerShriekFunctorCompIso f g).app (etaleModuleForget Λ F) ≪≫
    (lowerShriek g).mapIso (lowerShriekModule_forget f Λ F).symm ≪≫
    (lowerShriekModule_forget g Λ ((lowerShriekModule f Λ).obj F)).symm

/-- Module-level form of `lowerShriekFunctorCompIso`, obtained by lifting the
forgotten abelian identification along `forget₂`. -/
def weightingTraceModuleLowerShriekCompIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule (f ≫ g) Λ).obj F ≅
      (lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F) where
  hom :=
    liftModuleSheafHom
      (weightingTraceModuleLowerShriekCompForgetIso f g Λ F).hom
  inv :=
    liftModuleSheafHom
      (weightingTraceModuleLowerShriekCompForgetIso f g Λ F).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf-level identification
`(f ≫ g)_! (f ≫ g)⁻¹ F ≅ g_! f_! f⁻¹ g⁻¹ F` of étale sheaves of modules. -/
def weightingTraceModuleCompIso
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule (f ≫ g) Λ).obj
        ((etaleModuleSheafPullback (f ≫ g) Λ).obj F) ≅
      (lowerShriekModule g Λ).obj
        ((lowerShriekModule f Λ).obj
          ((etaleModuleSheafPullback f Λ).obj
            ((etaleModuleSheafPullback g Λ).obj F))) :=
  (lowerShriekModule (f ≫ g) Λ).mapIso
      ((etaleModuleSheafPullback_comp g f Λ).symm.app F) ≪≫
    weightingTraceModuleLowerShriekCompIso f g Λ
      ((etaleModuleSheafPullback f Λ).obj ((etaleModuleSheafPullback g Λ).obj F))

/-- Natural isomorphism packaging of `weightingTraceModuleCompIso`. -/
def weightingTraceModuleCompNatIso :
    etaleModuleSheafPullback (f ≫ g) Λ ⋙ lowerShriekModule (f ≫ g) Λ ≅
      etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f Λ ⋙
        lowerShriekModule f Λ ⋙ lowerShriekModule g Λ :=
  NatIso.ofComponents (weightingTraceModuleCompIso f g Λ) sorry

variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived identification `(f ≫ g)_! (f ≫ g)⁻¹ K ≅ g_! f_! f⁻¹ g⁻¹ K` on
`D(Z_étale, Λ)`, obtained by `ExactFunctor.MapDerivedCategory` of the
sheaf-level module identification after reassociating composites of exact
functors. -/
def weightingTraceDerivedCompIso (K : EtaleDerived Z Λ) :
    (lowerShriekModuleDerived (f ≫ g) Λ).obj
        ((etaleModuleDerivedInverseImage (f ≫ g) Λ).obj K) ≅
      (lowerShriekModuleDerived g Λ).obj
        ((lowerShriekModuleDerived f Λ).obj
          ((etaleModuleDerivedInverseImage f Λ).obj
            ((etaleModuleDerivedInverseImage g Λ).obj K))) :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (etaleModuleSheafPullback (f ≫ g) Λ))
      (ExactFunctor.of (lowerShriekModule (f ≫ g) Λ))).symm.app K ≪≫
    Functor.MapDerivedCategory.objIso (weightingTraceModuleCompNatIso f g Λ) K ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f Λ ⋙
            lowerShriekModule f Λ))
        (ExactFunctor.of (lowerShriekModule g Λ))).app K ≪≫
    (lowerShriekModuleDerived g Λ).mapIso
      ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of
            (etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f Λ))
          (ExactFunctor.of (lowerShriekModule f Λ))).app K) ≪≫
    (lowerShriekModuleDerived g Λ).mapIso
      ((lowerShriekModuleDerived f Λ).mapIso
        ((ExactFunctor.MapDerivedCategory.compFunctorIso
            (ExactFunctor.of (etaleModuleSheafPullback g Λ))
            (ExactFunctor.of (etaleModuleSheafPullback f Λ))).app K))

/-- The forward map of `weightingTraceDerivedCompIso` is the composite of the
exact-derived reassociations with `mapDerivedCategory` of
`weightingTraceModuleCompNatIso`. -/
theorem weightingTraceDerivedCompIso_hom (K : EtaleDerived Z Λ) :
    (weightingTraceDerivedCompIso f g Λ K).hom =
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (etaleModuleSheafPullback (f ≫ g) Λ))
          (ExactFunctor.of (lowerShriekModule (f ≫ g) Λ))).inv.app K ≫
        (Functor.MapDerivedCategory.objIso
          (weightingTraceModuleCompNatIso f g Λ) K).hom ≫
        (ExactFunctor.MapDerivedCategory.compFunctorIso
            (ExactFunctor.of
              (etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f Λ ⋙
                lowerShriekModule f Λ))
            (ExactFunctor.of (lowerShriekModule g Λ))).hom.app K ≫
        (lowerShriekModuleDerived g Λ).map
          ((ExactFunctor.MapDerivedCategory.compFunctorIso
              (ExactFunctor.of
                (etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f Λ))
              (ExactFunctor.of (lowerShriekModule f Λ))).hom.app K) ≫
        (lowerShriekModuleDerived g Λ).map
          ((lowerShriekModuleDerived f Λ).map
            ((ExactFunctor.MapDerivedCategory.compFunctorIso
                (ExactFunctor.of (etaleModuleSheafPullback g Λ))
                (ExactFunctor.of (etaleModuleSheafPullback f Λ))).hom.app K)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
