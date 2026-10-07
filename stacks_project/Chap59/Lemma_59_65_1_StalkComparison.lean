module

public import stacks_project.Chap59.Lemma_59_65_1_ModuleSheafInverse
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Specified stalk comparisons for the finite module-sheaf inverse

Representable germs are evaluated at their pointing. The inverse sends a point
to the identity germ. Sheafification and the set-level equivalence then supply
the concrete carrier maps for the module counit and sheaf unit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
open CategoryTheory.Action.ModuleCat
open scoped FintypeCatDiscrete

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleSheafInverse

variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)

/-- Evaluate a representable germ at its geometric pointing. -/
def representableFiberToPoint (Y : X.Etale) :
    (geometricPointEtalePoint xbar).presheafFiber.obj (uliftYoneda.{u + 1}.obj Y) ⟶
      ULift.{u + 1} ((geometricPointEtalePoint xbar).fiber.obj Y) :=
  (geometricPointEtalePoint xbar).presheafFiberDesc
    (fun U s ↦ TypeCat.ofHom fun f ↦
      ULift.up ((geometricPointEtalePoint xbar).fiber.map f.down s))
    (fun _ _ _ _ ↦ sorry)

/-- The inverse representable-fiber map sends a point to the germ of the identity section. -/
def pointToRepresentableFiber (Y : X.Etale) :
    ULift.{u + 1} ((geometricPointEtalePoint xbar).fiber.obj Y) ⟶
      (geometricPointEtalePoint xbar).presheafFiber.obj (uliftYoneda.{u + 1}.obj Y) :=
  TypeCat.ofHom fun s ↦
    (geometricPointEtalePoint xbar).toPresheafFiber Y s.down
      (uliftYoneda.{u + 1}.obj Y) (ULift.up (𝟙 Y))

/-- Evaluation followed by the identity germ recovers each representable germ. -/
theorem representableFiber_left_inv (Y : X.Etale)
    (s : (geometricPointEtalePoint xbar).presheafFiber.obj (uliftYoneda.{u + 1}.obj Y)) :
    pointToRepresentableFiber xbar Y (representableFiberToPoint xbar Y s) = s := sorry

/-- The identity germ evaluates to its specified point. -/
theorem representableFiber_right_inv (Y : X.Etale)
    (s : ULift.{u + 1} ((geometricPointEtalePoint xbar).fiber.obj Y)) :
    representableFiberToPoint xbar Y (pointToRepresentableFiber xbar Y s) = s := sorry

/-- The representable stalk comparison with both functions explicitly specified. -/
def representableFiberEquiv (Y : X.Etale) :
    (geometricPointEtalePoint xbar).presheafFiber.obj (uliftYoneda.{u + 1}.obj Y) ≃
      ULift.{u + 1} ((geometricPointEtalePoint xbar).fiber.obj Y) where
  toFun := representableFiberToPoint xbar Y
  invFun := pointToRepresentableFiber xbar Y
  left_inv := representableFiber_left_inv xbar Y
  right_inv := representableFiber_right_inv xbar Y

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]

/-- Sheafification does not alter the representable fiber; the comparison uses its actual unit. -/
def representedSheafFiberEquiv (Y : X.Etale) :
    (geometricPointEtalePoint xbar).sheafFiber.obj
        (X.smallEtaleTopology.sheafifiedRepresentable Y) ≃
      ULift.{u + 1} ((geometricPointEtalePoint xbar).fiber.obj Y) :=
  (((geometricPointEtalePoint xbar).presheafToSheafCompSheafFiberIso
      (Type (u + 1))).app (uliftYoneda.{u + 1}.obj Y)).toEquiv.trans
    (representableFiberEquiv xbar Y)

/-- The canonical actual-stalk/finite-action carrier comparison for a finite set sheaf. -/
def setStalkEquiv
    (F : (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory) :
    (geometricPointEtalePoint xbar).presheafFiber.obj F.obj.obj ≃
      ULift.{u + 1} (((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj F).obj.V) :=
  (((geometricPointEtalePoint xbar).sheafFiber.mapIso
      ((Sheaf.finiteLocallyConstant X.smallEtaleTopology).ι.mapIso
        ((finiteEtaleToFiniteLocallyConstant (X := X)).asEquivalence.counitIso.app F)).symm).toEquiv).trans
    (representedSheafFiberEquiv xbar
      (finiteEtaleToEtale ((finiteEtaleToFiniteLocallyConstant (X := X)).asEquivalence.inverse.obj F)))

/-- Forget a finite-action isomorphism to its actual equivalence of underlying finite sets. -/
def actionIsoEquiv
    {S T : ContAction FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar))} (e : S ≅ T) :
    S.obj.V ≃ T.obj.V :=
  (((CategoryTheory.forget₂ (ContAction FintypeCat.{u} (Aut (standardFiniteEtaleFiber xbar)))
      FintypeCat.{u}) ⋙ FintypeCat.incl).mapIso e).toEquiv

variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- Forgetting modules preserves the smaller filtered colimits used by the site point. -/
instance forgetModule_preservesPointColimits :
    PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))

/-- The actual module fiber has the same carrier as the fiber of its underlying presheaf. -/
def moduleFiberForgetEquiv (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (StalkRepresentation.stalk Λ xbar).obj F ≃
      (geometricPointEtalePoint xbar).presheafFiber.obj
        (F.obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  (((geometricPointEtalePoint xbar).presheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F.obj).symm.toEquiv

/-- The counit carrier map combines actual stalk comparison and the specified set counit. -/
def counitEquiv
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (StalkRepresentation.stalk Λ xbar).obj (sheaf Λ xbar M) ≃ M.obj.obj.V :=
  (moduleFiberForgetEquiv xbar Λ (sheaf Λ xbar M)).trans
    ((setStalkEquiv xbar
      ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).inverse.obj (moduleSet Λ xbar M))).trans
      (Equiv.ulift.trans ((actionIsoEquiv xbar (underlyingSetCounit Λ xbar M)).trans
        (carrierEquiv Λ xbar M).symm)))

/-- The specified stalk counit preserves the transported addition. -/
theorem counitEquiv_add
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory)
    (s t : (StalkRepresentation.stalk Λ xbar).obj (sheaf Λ xbar M)) :
    counitEquiv xbar Λ M (s + t) = counitEquiv xbar Λ M s + counitEquiv xbar Λ M t := sorry

/-- The specified stalk counit preserves the transported scalar action. -/
theorem counitEquiv_smul
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory)
    (a : Λ) (s : (StalkRepresentation.stalk Λ xbar).obj (sheaf Λ xbar M)) :
    counitEquiv xbar Λ M (a • s) = a • counitEquiv xbar Λ M s := sorry

/-- The actual module-stalk counit, with inverse supplied by the explicit carrier equivalence. -/
def counitLinearEquiv
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (StalkRepresentation.stalk Λ xbar).obj (sheaf Λ xbar M) ≃ₗ[Λ] M.obj.obj.V where
  __ := counitEquiv xbar Λ M
  map_add' := counitEquiv_add xbar Λ M
  map_smul' := counitEquiv_smul xbar Λ M

/-- The specified linear counit commutes with the published stalk-monodromy action. -/
theorem counit_equivariant
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
    ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj
      ((finiteFunctor Λ xbar).obj M)).obj.obj.ρ σ ≫ (counitLinearEquiv xbar Λ M).toModuleIso.hom =
      (counitLinearEquiv xbar Λ M).toModuleIso.hom ≫ M.obj.obj.ρ σ := sorry

/-- The equivariant counit uses the actual linear stalk map and its specified inverse. -/
def counitApp
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj
      ((finiteFunctor Λ xbar).obj M) ≅ M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso (counitLinearEquiv xbar Λ M).toModuleIso (counit_equivariant xbar Λ M)))

/-- Naturality of the prescribed equivariant stalk counit in coefficient morphisms. -/
theorem counitApp_naturality
    {M N : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory}
    (f : M ⟶ N) :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).map
        ((finiteFunctor Λ xbar).map f) ≫ (counitApp xbar Λ N).hom =
      (counitApp xbar Λ M).hom ≫ f := sorry

/-- The module-representation counit as a natural isomorphism. -/
def counitIso :
    finiteFunctor Λ xbar ⋙ finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ counitApp xbar Λ M) (fun f ↦ counitApp_naturality xbar Λ f)

/-- The underlying set sheaf of a module sheaf, retaining the exact presheaf maps. -/
def underlyingSheaf (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ⟨F.obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ),
    (Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology F.obj
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).mp F.property⟩

/-- Finite coefficients make the underlying sheaf of a finite-type local system finite. -/
theorem underlyingSheaf_finite
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    Sheaf.IsFiniteLocallyConstant (underlyingSheaf Λ F.obj) := sorry

/-- The actual finite underlying set sheaf used by the set-level unit. -/
def underlyingFiniteSheaf
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory :=
  ⟨underlyingSheaf Λ F.obj, underlyingSheaf_finite Λ F⟩

/-- The set-level fiber and the small carrier of the published module stalk have a specified equivalence. -/
def forwardCarrierEquiv
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      (underlyingFiniteSheaf Λ F)).obj.V ≃
      Carrier Λ xbar ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F) :=
  (Equiv.ulift.symm.trans (setStalkEquiv xbar (underlyingFiniteSheaf Λ F)).symm).trans
    ((moduleFiberForgetEquiv xbar Λ F.obj).symm.trans
      (carrierEquiv Λ xbar ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F)))

/-- A finite-set isomorphism with its forward and inverse functions explicitly supplied. -/
def finiteSetIso {A B : FintypeCat.{u}} (e : A ≃ B) : A ≅ B where
  hom := FintypeCat.homMk e
  inv := FintypeCat.homMk e.symm
  hom_inv_id := by
    apply FintypeCat.hom_ext
    intro a
    exact e.symm_apply_apply a
  inv_hom_id := by
    apply FintypeCat.hom_ext
    intro b
    exact e.apply_symm_apply b

/-- The finite-set/stalk comparison is equivariant for the natural fiber actions. -/
theorem forwardCarrierEquiv_equivariant
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      (underlyingFiniteSheaf Λ F)).obj.ρ σ ≫
        (finiteSetIso (forwardCarrierEquiv xbar Λ F)).hom =
      (finiteSetIso (forwardCarrierEquiv xbar Λ F)).hom ≫
        (moduleSet Λ xbar
          ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F)).obj.ρ σ := sorry

/-- The specified equivariant comparison between the set forward functor and the published module forward functor. -/
def forwardSetIso
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      (underlyingFiniteSheaf Λ F) ≅
        moduleSet Λ xbar ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F) :=
  ObjectProperty.isoMk _
    (Action.mkIso (finiteSetIso (forwardCarrierEquiv xbar Λ F))
      (forwardCarrierEquiv_equivariant xbar Λ F))

/-- The underlying sheaf unit is the set-level unit followed by the transported stalk comparison. -/
def unitSetIso
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    underlyingSheaf Λ F.obj ≅
      setSheaf xbar (moduleSet Λ xbar
        ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F)) :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).ι.mapIso
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).unitIso.app
        (underlyingFiniteSheaf Λ F) ≪≫
      (finiteLocallyConstant_equivalence_finitePi1Sets xbar).inverse.mapIso (forwardSetIso xbar Λ F))

/-- The sectionwise carrier equivalence of the actual sheaf unit. -/
def unitSectionEquiv
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etaleᵒᵖ) :
    F.obj.obj.obj U ≃
      Sections Λ xbar ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F) U :=
  (((sheafToPresheaf X.smallEtaleTopology (Type (u + 1))).mapIso (unitSetIso xbar Λ F)).app U).toEquiv

/-- The specified sectionwise sheaf unit preserves addition. -/
theorem unitSectionEquiv_add
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etaleᵒᵖ) (s t : F.obj.obj.obj U) :
    unitSectionEquiv xbar Λ F U (s + t) =
      unitSectionEquiv xbar Λ F U s + unitSectionEquiv xbar Λ F U t := sorry

/-- The specified sectionwise sheaf unit preserves scalar multiplication. -/
theorem unitSectionEquiv_smul
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etaleᵒᵖ) (a : Λ) (s : F.obj.obj.obj U) :
    unitSectionEquiv xbar Λ F U (a • s) = a • unitSectionEquiv xbar Λ F U s := sorry

/-- The actual linear equivalence on sections underlying the sheaf unit. -/
def unitSectionLinearEquiv
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (U : X.Etaleᵒᵖ) :
    F.obj.obj.obj U ≃ₗ[Λ]
      Sections Λ xbar ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F) U where
  __ := unitSectionEquiv xbar Λ F U
  map_add' := unitSectionEquiv_add xbar Λ F U
  map_smul' := unitSectionEquiv_smul xbar Λ F U

/-- The prescribed sectionwise unit is natural in restriction maps. -/
theorem unitSection_naturality
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    F.obj.obj.map f ≫ (unitSectionLinearEquiv xbar Λ F V).toModuleIso.hom =
      (unitSectionLinearEquiv xbar Λ F U).toModuleIso.hom ≫
        (sheaf Λ xbar ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F)).obj.map f := sorry

/-- The actual module-sheaf unit, obtained from the specified linear section equivalences. -/
def unitSheafIso
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    F.obj ≅ sheaf Λ xbar ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F) :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ (unitSectionLinearEquiv xbar Λ F U).toModuleIso)
      (fun f ↦ unitSection_naturality xbar Λ F f))

/-- The sheaf unit in the finite locally constant module subcategory. -/
def unitApp
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    F ≅ (finiteFunctor Λ xbar).obj
      ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F) :=
  ObjectProperty.isoMk _ (unitSheafIso xbar Λ F)

/-- Naturality of the prescribed sheaf unit in module-sheaf morphisms. -/
theorem unitApp_naturality
    {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) :
    f ≫ (unitApp xbar Λ G).hom = (unitApp xbar Λ F).hom ≫
      (finiteFunctor Λ xbar).map
        ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).map f) := sorry

/-- The module-sheaf unit as a natural isomorphism, with the set-level unit as its origin. -/
def unitIso :
    𝟭 _ ≅ finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar ⋙ finiteFunctor Λ xbar :=
  NatIso.ofComponents (fun F ↦ unitApp xbar Λ F) (fun f ↦ unitApp_naturality xbar Λ f)

/-- The forward triangle law for the specified sheaf unit and stalk counit. -/
theorem forward_triangle
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).map ((unitIso xbar Λ).hom.app F) ≫
      (counitIso xbar Λ).hom.app
        ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj F) = 𝟙 _ := sorry

/-- The concrete finite-module equivalence with the published forward functor unchanged. -/
def equivalence :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
      (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory where
  functor := finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar
  inverse := finiteFunctor Λ xbar
  unitIso := unitIso xbar Λ
  counitIso := counitIso xbar Λ
  functor_unitIso_comp := forward_triangle xbar Λ

/-- The second triangle follows from the first for the same prescribed unit and counit. -/
theorem inverse_triangle
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (unitIso xbar Λ).hom.app ((finiteFunctor Λ xbar).obj M) ≫
      (finiteFunctor Λ xbar).map ((counitIso xbar Λ).hom.app M) = 𝟙 _ :=
  (equivalence xbar Λ).unit_inverse_comp M

end AlgebraicGeometry.Scheme.ModuleSheafInverse
