module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap63.Lemma_63_4_10
public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_5_2
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
public import stacks_project.Chap63.Lemma_63_8_5_Pullback

/-!
# Functoriality, base change, and derived weighting traces

The sheaf-level weighting trace `Tr_{f, w, F}` is packaged as a natural
transformation, compared with its cartesian base change, and lifted to
`Tr_{f, w, K}` on `D(Y_étale, Λ)` by applying the exact functors `f_!` and
`f⁻¹` to representing complexes of `Λ`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y X' Y' : Scheme.{u}}
variable {f : X ⟶ Y} [LocallyQuasiFinite f]
variable {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- A weighting of a locally quasi-finite morphism remains a weighting after
transport along an arbitrary cartesian square, with `w' = w ∘ g'`. -/
theorem IsWeighting.of_isPullback {w : X → ℤ} (hw : f.IsWeighting w)
    [LocallyQuasiFinite f'] (h_cart : IsPullback g' f' f g) :
    f'.IsWeighting (fun x' ↦ w (g' x')) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The weighting trace as a natural transformation
`f_! ∘ f⁻¹ ⟶ 𝟭` on abelian étale sheaves. -/
def weightingTraceNatTrans {w : X → ℤ} (hw : f.IsWeighting w) :
    etaleAbelianSheafPullback f ⋙ lowerShriek f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) where
  app F := weightingTrace f hw F
  naturality := sorry

/-- Components of `weightingTraceNatTrans` are the sheaf traces
`weightingTrace`. -/
theorem weightingTraceNatTrans_app {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingTraceNatTrans f hw).app F = weightingTrace f hw F :=
  sorry

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]

/-- Left vertical identification of the weighting-trace base-change square:
`g⁻¹ f_! f⁻¹ F ≅ f'_! (g')⁻¹ f⁻¹ F ≅ f'_! (f')⁻¹ g⁻¹ F`, using
`lowerShriekBaseChangeIso` and `etaleAbelianSheafPullback_square`. -/
def weightingTraceBaseChangeIso
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj
        ((lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F)) ≅
      (lowerShriek f').obj
        ((etaleAbelianSheafPullback f').obj
          ((etaleAbelianSheafPullback g).obj F)) :=
  (lowerShriekBaseChangeIso_app f g f' g' h_cart
      ((etaleAbelianSheafPullback f).obj F)).trans
    ((lowerShriek f').mapIso
      ((etaleAbelianSheafPullback_square f g f' g' h_cart).symm.app F))

/-- The weighting trace on the cartesian base change, for the pulled-back
weighting `w ∘ g'`. -/
def weightingTrace_isPullback {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f').obj ((etaleAbelianSheafPullback f').obj F) ⟶ F :=
  weightingTrace f' (w := fun x' ↦ w (g' x')) (IsWeighting.of_isPullback hw h_cart) F

/-- The forward map of `weightingTraceBaseChangeIso` is the composite of the
lower-shriek base-change isomorphism with the inverse-image square. -/
theorem weightingTraceBaseChangeIso_hom
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (weightingTraceBaseChangeIso f g f' g' h_cart F).hom =
      (lowerShriekBaseChangeIso_app f g f' g' h_cart
          ((etaleAbelianSheafPullback f).obj F)).hom ≫
        (lowerShriek f').map
          ((etaleAbelianSheafPullback_square f g f' g' h_cart).inv.app F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Lift an abelian sheaf morphism between forgotten module sheaves to a
morphism of sheaves of `Λ`-modules, using the underlying additive map on
sections. -/
def liftModuleSheafHom {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α :
      (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
        (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G) :
    F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U ↦
        ConcreteCategory.ofHom (C := ModuleCat.{u} Λ)
          { toAddHom := (α.hom.app U).hom.toAddHom
            map_smul' := fun _ _ ↦ sorry }
      naturality := sorry }

/-- The lift recovers the original abelian sheaf morphism after forgetting
coefficients. -/
theorem sheafCompose_map_liftModuleSheafHom {S : Scheme.{u}} {Λ : Type u}
    [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α :
      (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
        (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G) :
    (sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).map
        (liftModuleSheafHom α) =
      α :=
  sorry

variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]

/-- Forgotten abelian form of the module-level weighting trace, before lifting
coefficients. -/
def weightingTraceModuleForgetHom {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f Λ).obj ((etaleModuleSheafPullback f Λ).obj F)) ⟶
      (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F :=
  (lowerShriekModule_forget f Λ ((etaleModuleSheafPullback f Λ).obj F)).hom ≫
    (lowerShriek f).map
      ((etaleModuleSheafPullback_compSheafComposeIso f Λ).hom.app F) ≫
      weightingTrace f hw (etaleModuleForget Λ F)

/-- The sheaf-level `Λ`-linear weighting trace at a sheaf of modules. -/
def weightingTraceModuleHom {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule f Λ).obj ((etaleModuleSheafPullback f Λ).obj F) ⟶ F :=
  liftModuleSheafHom (weightingTraceModuleForgetHom f Λ hw F)

/-- Evaluating the module-level trace recovers the lift of the forgotten
abelian trace. -/
theorem weightingTraceModuleHom_eq {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    weightingTraceModuleHom f Λ hw F =
      liftModuleSheafHom (weightingTraceModuleForgetHom f Λ hw F) :=
  sorry

/-- The `Λ`-linear weighting trace as a natural transformation
`f_! ∘ f⁻¹ ⟶ 𝟭` on étale sheaves of modules. -/
def weightingTraceModuleNatTrans {w : X → ℤ} (hw : f.IsWeighting w) :
    etaleModuleSheafPullback f Λ ⋙ lowerShriekModule f Λ ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) where
  app F := weightingTraceModuleHom f Λ hw F
  naturality := sorry

/-- Components of `weightingTraceModuleNatTrans` are `weightingTraceModuleHom`. -/
theorem weightingTraceModuleNatTrans_app {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (weightingTraceModuleNatTrans f Λ hw).app F =
      weightingTraceModuleHom f Λ hw F :=
  sorry

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived natural transformation of the weighting trace, obtained by
`ExactFunctor.MapDerivedCategory.map` of the sheaf-level module trace and
reassociating the composite `f_! ∘ f⁻¹`. -/
def weightingTraceDerivedNatTrans {w : X → ℤ} (hw : f.IsWeighting w) :
    etaleModuleDerivedInverseImage f Λ ⋙ lowerShriekModuleDerived f Λ ⟶
      𝟭 (EtaleDerived Y Λ) :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of (etaleModuleSheafPullback f Λ))
        (ExactFunctor.of (lowerShriekModule f Λ))).inv ≫
    ExactFunctor.MapDerivedCategory.map
      (ObjectProperty.homMk (weightingTraceModuleNatTrans f Λ hw) :
        (ExactFunctor.of (etaleModuleSheafPullback f Λ)).comp
            (ExactFunctor.of (lowerShriekModule f Λ)) ⟶
          ExactFunctor.id (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
    (ExactFunctor.MapDerivedCategory.idFunctorIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).hom

/-- Objectwise derived weighting trace `Tr_{f, w, K} : f_! f⁻¹ K ⟶ K`. -/
def weightingTraceDerivedHom {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y Λ) :
    (lowerShriekModuleDerived f Λ).obj
        ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K :=
  (weightingTraceDerivedNatTrans f Λ hw).app K

/-- The objectwise derived trace is the component of
`weightingTraceDerivedNatTrans`. -/
theorem weightingTraceDerivedHom_eq {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y Λ) :
    weightingTraceDerivedHom f Λ hw K =
      (weightingTraceDerivedNatTrans f Λ hw).app K :=
  sorry

/-- Functoriality of the derived weighting trace in `K`. -/
theorem weightingTraceDerived_natural {w : X → ℤ} (hw : f.IsWeighting w)
    {K L : EtaleDerived Y Λ} (φ : K ⟶ L) :
    (lowerShriekModuleDerived f Λ).map
          ((etaleModuleDerivedInverseImage f Λ).map φ) ≫
        weightingTraceDerivedHom f Λ hw L =
      weightingTraceDerivedHom f Λ hw K ≫ φ :=
  sorry

section DerivedBaseChange

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f').op]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Forgetting coefficients identifies the module-level compact-support
comparison `g⁻¹ f_! ≅ f'_! (g')⁻¹` with the abelian isomorphism
`lowerShriekBaseChangeIso`. -/
def weightingTraceModuleLowerShriekForgetIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModuleSheafPullback g Λ).obj ((lowerShriekModule f Λ).obj F)) ≅
      (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f' Λ).obj ((etaleModuleSheafPullback g' Λ).obj F)) :=
  (etaleModuleSheafPullback_compSheafComposeIso g Λ).app
      ((lowerShriekModule f Λ).obj F) ≪≫
    (etaleAbelianSheafPullback g).mapIso (lowerShriekModule_forget f Λ F) ≪≫
    lowerShriekBaseChangeIso_app f g f' g' h_cart (etaleModuleForget Λ F) ≪≫
    (lowerShriek f').mapIso
      ((etaleModuleSheafPullback_compSheafComposeIso g' Λ).app F).symm ≪≫
    (lowerShriekModule_forget f' Λ ((etaleModuleSheafPullback g' Λ).obj F)).symm

/-- Module-level form of `lowerShriekBaseChangeIso_app`, obtained by lifting
the forgotten abelian identification along `forget₂`. -/
def weightingTraceModuleLowerShriekIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModuleSheafPullback g Λ).obj ((lowerShriekModule f Λ).obj F) ≅
      (lowerShriekModule f' Λ).obj ((etaleModuleSheafPullback g' Λ).obj F) where
  hom :=
    liftModuleSheafHom
      (weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).hom
  inv :=
    liftModuleSheafHom
      (weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf-level left vertical identification of the module weighting-trace
base-change square: `g⁻¹ f_! f⁻¹ F ≅ f'_! (g')⁻¹ f⁻¹ F ≅ f'_! (f')⁻¹ g⁻¹ F`. -/
def weightingTraceModuleBaseChangeIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleModuleSheafPullback g Λ).obj
        ((lowerShriekModule f Λ).obj ((etaleModuleSheafPullback f Λ).obj F)) ≅
      (lowerShriekModule f' Λ).obj
        ((etaleModuleSheafPullback f' Λ).obj
          ((etaleModuleSheafPullback g Λ).obj F)) :=
  (weightingTraceModuleLowerShriekIso f Λ g f' g' h_cart
      ((etaleModuleSheafPullback f Λ).obj F)).trans
    ((lowerShriekModule f' Λ).mapIso
      ((etaleModuleSheafPullback_square f g f' g' h_cart Λ).symm.app F))

/-- The forward map of `weightingTraceModuleBaseChangeIso` is the compact-support
comparison followed by `etaleModuleSheafPullback_square.symm`. -/
theorem weightingTraceModuleBaseChangeIso_hom
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart F).hom =
      (weightingTraceModuleLowerShriekIso f Λ g f' g' h_cart
          ((etaleModuleSheafPullback f Λ).obj F)).hom ≫
        (lowerShriekModule f' Λ).map
          ((etaleModuleSheafPullback_square f g f' g' h_cart Λ).inv.app F) :=
  sorry

/-- Natural isomorphism packaging of `weightingTraceModuleBaseChangeIso`. -/
def weightingTraceModuleBaseChangeNatIso :
    etaleModuleSheafPullback f Λ ⋙ lowerShriekModule f Λ ⋙
        etaleModuleSheafPullback g Λ ≅
      etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f' Λ ⋙
        lowerShriekModule f' Λ :=
  NatIso.ofComponents
    (fun F ↦ weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart F) sorry

/-- Derived left-vertical identification of the weighting-trace base-change
square, obtained by `ExactFunctor.MapDerivedCategory` of the sheaf-level
module identification after reassociating composites of exact functors. -/
def weightingTraceDerivedBaseChangeIso (K : EtaleDerived Y Λ) :
    (etaleModuleDerivedInverseImage g Λ).obj
        ((lowerShriekModuleDerived f Λ).obj
          ((etaleModuleDerivedInverseImage f Λ).obj K)) ≅
      (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage f' Λ).obj
          ((etaleModuleDerivedInverseImage g Λ).obj K)) :=
  (etaleModuleDerivedInverseImage g Λ).mapIso
      ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (etaleModuleSheafPullback f Λ))
          (ExactFunctor.of (lowerShriekModule f Λ))).symm.app K) ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (etaleModuleSheafPullback f Λ ⋙ lowerShriekModule f Λ))
        (ExactFunctor.of (etaleModuleSheafPullback g Λ))).symm.app K ≪≫
    Functor.MapDerivedCategory.objIso
      (weightingTraceModuleBaseChangeNatIso f Λ g f' g' h_cart) K ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f' Λ))
        (ExactFunctor.of (lowerShriekModule f' Λ))).app K ≪≫
    (lowerShriekModuleDerived f' Λ).mapIso
      ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (etaleModuleSheafPullback g Λ))
          (ExactFunctor.of (etaleModuleSheafPullback f' Λ))).app K)

/-- The derived weighting trace on a cartesian base change, for the
pulled-back weighting `w ∘ g'`. -/
def weightingTraceDerived_isPullback {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y' Λ) :
    (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage f' Λ).obj K) ⟶ K :=
  weightingTraceDerivedHom f' Λ (w := fun x' ↦ w (g' x'))
    (IsWeighting.of_isPullback hw h_cart) K

/-- The base-changed derived trace is `weightingTraceDerivedHom` for
`w ∘ g'`. -/
theorem weightingTraceDerived_isPullback_eq {w : X → ℤ}
    (hw : f.IsWeighting w) (K : EtaleDerived Y' Λ) :
    weightingTraceDerived_isPullback f Λ g f' g' h_cart hw K =
      weightingTraceDerivedHom f' Λ (w := fun x' ↦ w (g' x'))
        (IsWeighting.of_isPullback hw h_cart) K :=
  sorry

/-- Derived weighting traces are compatible with arbitrary cartesian base
change: `g⁻¹ Tr_{f, w, K} = iso.hom ≫ Tr_{f', w ∘ g', g⁻¹ K}`. -/
theorem weightingTraceDerived_baseChange {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y Λ) :
    (etaleModuleDerivedInverseImage g Λ).map
        (weightingTraceDerivedHom f Λ hw K) =
      (weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart K).hom ≫
        weightingTraceDerived_isPullback f Λ g f' g' h_cart hw
          ((etaleModuleDerivedInverseImage g Λ).obj K) :=
  sorry

end DerivedBaseChange

end AlgebraicGeometry.Scheme.Etale

end
