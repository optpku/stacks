module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The sheaf-valued derived internal-Hom bifunctor

Derived arrows into the actual K-injective models lift through the proved bijection on
homotopy classes. The strict internal-Hom action then supplies the morphism action. The
comparison with the existing source model keeps the original object presentation unchanged.
The output is the derived category of module sheaves on this site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite SheafOfModules.RingedSite.RingedSiteDerived

noncomputable section

universe u v

namespace RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The actual product-valued cochain internal-Hom bifunctor on module sheaves. -/
def strictInternalHom :
    (CochainComplex (ringedSiteModuleCategory J O) ℤ)ᵒᵖ ⥤
      CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
        CochainComplex (ringedSiteModuleCategory J O) ℤ := by
  let tensorExists : ∀ X Y : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor X Y :=
    fun _ _ _ ↦ HasColimitsOfShape.has_colimit _
  let goodLeft : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let goodRight : ∀ X Y Z : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
    fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let tensorExt : ∀ X Y Z W : GradedObject ℤ (ringedSiteModuleCategory J O),
      GradedObject.HasTensor₄ObjExt X Y Z W :=
    fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesLeft : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let preservesRight : ∀ X, PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J O))
      ((curriedTensor (ringedSiteModuleCategory J O)).flip.obj X) :=
    fun _ ↦ PreservesColimitsOfShape.preservesColimit
  let closed := @CochainComplex.InternalHom.monoidalClosed
    (ringedSiteModuleCategory J O)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance tensorExists goodLeft goodRight tensorExt
    preservesLeft preservesRight
  exact @MonoidalClosed.internalHom _ inferInstance _ closed

/-- On two strict complexes, the bifunctor has the existing actual sheaf-Hom model. -/
theorem strictInternalHom_obj (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) :
    (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj
        ((strictInternalHom.obj (op F)).obj I) = objOfModels F I := rfl

/-- Lift a specified derived arrow into a K-injective model through the actual bijection on
homotopy classes, then take a representative cochain map. -/
def liftToInjectiveModel (F : CochainComplex (ringedSiteModuleCategory J O) ℤ)
    (N : max J O)
    (f : (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj F ⟶ N) :
    F ⟶ injectiveModel N :=
  (HomotopyCategory.quotient (ringedSiteModuleCategory J O) (.up ℤ)).preimage
    ((Equiv.ofBijective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient (ringedSiteModuleCategory J O) (.up ℤ)).obj F ⟶
          (HomotopyCategory.quotient (ringedSiteModuleCategory J O) (.up ℤ)).obj
            (injectiveModel N)) → _)
      (CochainComplex.IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient (ringedSiteModuleCategory J O) (.up ℤ)).obj F)
        (injectiveModel N))).symm
      ((DerivedCategory.quotientCompQhIso (ringedSiteModuleCategory J O)).hom.app F ≫
        f ≫ (injectiveModelIso N).inv ≫
          (DerivedCategory.quotientCompQhIso (ringedSiteModuleCategory J O)).inv.app
            (injectiveModel N)))

/-- The chosen cochain representative realizes the specified derived arrow. -/
@[reassoc]
theorem liftToInjectiveModel_fac (F : CochainComplex (ringedSiteModuleCategory J O) ℤ)
    (N : max J O)
    (f : (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).obj F ⟶ N) :
    DerivedCategory.Q.map (liftToInjectiveModel F N f) ≫ (injectiveModelIso N).hom = f := sorry

/-- A representative cochain map between the specified K-injective models of a derived arrow. -/
def modelMap {M N : max J O} (f : M ⟶ N) :
    injectiveModel M ⟶ injectiveModel N :=
  liftToInjectiveModel (injectiveModel M) N ((injectiveModelIso M).hom ≫ f)

/-- Compare the existing arbitrary source model to its actual K-injective model. -/
def sourceToInjectiveModel (M : max J O) :
    (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).objPreimage M ⟶
      injectiveModel M :=
  liftToInjectiveModel
    ((DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O).objPreimage M)
    M (Functor.objObjPreimageIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) M).hom

/-- The source-model comparison represents an isomorphism in the derived category. -/
instance sourceToInjectiveModel_quasiIso (M : max J O) :
    QuasiIso (sourceToInjectiveModel M) := sorry

/-- Actual precomposition on the strict sheaf Hom compares the two source presentations. -/
def modelComparisonMap (M N : max J O) :
    objOfModels (injectiveModel M) (injectiveModel N) ⟶ obj M N :=
  DerivedCategory.Q.map
    ((strictInternalHom.map (sourceToInjectiveModel M).op).app (injectiveModel N))

/-- Sheaf internal Hom into a K-injective target sends the actual source comparison
quasi-isomorphism to a quasi-isomorphism, as in Stacks' well-definedness argument. -/
instance modelComparisonMap_isIso (M N : max J O) :
    IsIso (modelComparisonMap M N) := sorry

/-- The canonical comparison fixes its forward map as actual source precomposition. -/
def modelComparisonIso (M N : max J O) :
    objOfModels (injectiveModel M) (injectiveModel N) ≅ obj M N :=
  asIso (modelComparisonMap M N)

/-- The comparison's forward morphism is the displayed actual strict precomposition. -/
@[simp]
theorem modelComparisonIso_hom (M N : max J O) :
    (modelComparisonIso M N).hom = modelComparisonMap M N := rfl

/-- The morphism action of sheaf-valued derived internal Hom, contravariant in its source and
covariant in its target, transported from actual K-injective-model maps. -/
def map {M₁ M₂ N₁ N₂ : max J O} (f : M₂ ⟶ M₁) (g : N₁ ⟶ N₂) :
    obj M₁ N₁ ⟶ obj M₂ N₂ :=
  (modelComparisonIso M₁ N₁).inv ≫
    DerivedCategory.Q.map
      ((strictInternalHom.map (modelMap f).op).app (injectiveModel N₁) ≫
        (strictInternalHom.obj (op (injectiveModel M₂))).map (modelMap g)) ≫
    (modelComparisonIso M₂ N₂).hom

/-- The derived internal-Hom action sends identity morphisms to the identity morphism. -/
theorem map_id (M N : max J O) : map (𝟙 M) (𝟙 N) = 𝟙 (obj M N) := by
  sorry

/-- The derived internal-Hom action preserves composition, contravariantly in the source
and covariantly in the target. -/
theorem map_comp {M₁ M₂ M₃ N₁ N₂ N₃ : max J O}
    (f₁ : M₂ ⟶ M₁) (f₂ : M₃ ⟶ M₂) (g₁ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) :
    map (f₂ ≫ f₁) (g₁ ≫ g₂) = map f₁ g₁ ≫ map f₂ g₂ := by
  sorry

/-- The sheaf-valued derived internal-Hom bifunctor on this actual derived module category. -/
def functor : (max J O)ᵒᵖ × max J O ⥤ max J O where
  obj MN := obj MN.1.unop MN.2
  map f := map f.1.unop f.2
  map_id MN := map_id MN.1.unop MN.2
  map_comp f g := map_comp f.1.unop g.1.unop f.2 g.2

/-- The bifunctor reuses the existing object presentation of derived sheaf internal Hom. -/
@[simp]
theorem functor_obj (M N : max J O) : functor.obj (op M, N) = obj M N := rfl

/-- Currying preserves the source-first convention of the sheaf-valued bifunctor. -/
def curried : (max J O)ᵒᵖ ⥤ max J O ⥤ max J O :=
  Functor.curry.obj functor

/-- The source-variable derived sheaf internal-Hom functor. -/
def sourceFunctor (N : max J O) : (max J O)ᵒᵖ ⥤ max J O :=
  curried.flip.obj N

/-- The target-variable derived sheaf internal-Hom functor. -/
def targetFunctor (M : max J O) : max J O ⥤ max J O :=
  curried.obj (op M)

/-- Source-variable morphisms compute by the actual source precomposition action. -/
@[simp]
theorem sourceFunctor_map (N : max J O) {M₁ M₂ : max J O} (f : M₂ ⟶ M₁) :
    (sourceFunctor N).map f.op = map f (𝟙 N) := rfl

/-- Target-variable morphisms compute by the actual target postcomposition action. -/
@[simp]
theorem targetFunctor_map (M : max J O) {N₁ N₂ : max J O} (g : N₁ ⟶ N₂) :
    (targetFunctor M).map g = map (𝟙 M) g := rfl

end RingedSite.Hom.ModuleDerived.InternalHom
