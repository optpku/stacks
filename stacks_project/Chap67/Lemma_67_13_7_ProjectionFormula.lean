module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf

/-!
# Ringed-topos morphisms from étale ring maps and the projection-formula mate

A homomorphism `A ⟶ f_small,* B` of étale ring sheaves presents a morphism of small étale
ringed topoi. The associated module adjunction supplies the canonical projection-formula map
`F ⊗ f_* G ⟶ f_*(f^* F ⊗ G)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Sheaf.InternalModule
open RingedSite RingedSite.ToposHom
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The small étale ringed site of an algebraic space with a chosen commutative ring sheaf. -/
abbrev etaleRingedSite (X : AlgebraicSpace S)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    RingedSite.{u + 1, u, u} :=
  ofCommRingSheaf (smallEtaleTopology X) A

/-- The structure sheaf of `etaleRingedSite X A` is the underlying ring sheaf of `A`. -/
theorem etaleRingedSite_structureSheaf {X : AlgebraicSpace S}
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (etaleRingedSite X A).structureSheaf = Sheaf.ringSheafOfComm A :=
  rfl

/-- Direct-image ring compatibility for a homomorphism `A ⟶ f_small,* B` of étale ring sheaves. -/
theorem toRingedToposHom_isRingCompatible {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf) :
    @ToposHom.Direct.IsRingCompatible (etaleRingedSite X B) (etaleRingedSite Y A) _ _
      (morphismOfTopoi f) (ringPushforward f) (ringPushforwardForgetIso f) φ :=
  sorry

/-- The morphism of small étale ringed topoi associated to a homomorphism
`A ⟶ f_small,* B` of sheaves of rings. -/
def toRingedToposHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf) :
    ToposHom (etaleRingedSite X B) (etaleRingedSite Y A) :=
  @ToposHom.ofDirectImage (etaleRingedSite X B) (etaleRingedSite Y A) _ _
    (morphismOfTopoi f) (ringPushforward f) (ringPushforwardForgetIso f) φ
    (toRingedToposHom_isRingCompatible f φ)

/-- The underlying morphism of topoi of `toRingedToposHom f φ` is `morphismOfTopoi f`. -/
theorem toRingedToposHom_toTopos {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf) :
    (toRingedToposHom f φ).toTopos = morphismOfTopoi f :=
  rfl

/-- After forgetting to type-valued sheaves, the direct-image structure map of
`toRingedToposHom f φ` is the image of `φ` under `ringPushforwardForgetIso f`. -/
theorem toRingedToposHom_directStructureMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf) :
    (toRingedToposHom f φ).underlyingDirectImageMap =
      @ToposHom.Direct.underlyingMap (etaleRingedSite X B) (etaleRingedSite Y A) _ _
        (morphismOfTopoi f) (ringPushforward f) (ringPushforwardForgetIso f) φ :=
  sorry

/-- Restriction of scalars along the inverse-image structure map of `toRingedToposHom f φ`
is a right adjoint. -/
instance restrictScalars_toRingedToposHom_isRightAdjoint {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf) :
    (SheafOfModules.restrictScalars.{u} (toRingedToposHom f φ).structureMap).IsRightAdjoint :=
  sorry

/-- Sections of the ringed-topos direct image of a commutative ring sheaf commute. -/
theorem ringDirectImage_mul_comm {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (a b : ((toRingedToposHom f φ).toTopos.ringDirectImage.obj
      (etaleRingedSite X B).structureSheaf).obj.obj U) :
    a * b = b * a :=
  sorry

/-- Direct image of a commutative étale ring sheaf remains commutative on sections. -/
instance ringDirectImage_commRing {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    CommRing (((toRingedToposHom f φ).toTopos.ringDirectImage.obj
      (etaleRingedSite X B).structureSheaf).obj.obj U) where
  mul_comm := ringDirectImage_mul_comm f φ U

/-- The canonical lax comparison `f_*P × f_*Q ⟶ f_*(P × Q)` of type-valued étale
direct image, the adjunct of the oplax product comparison of inverse image followed
by the tensor of adjunction counits. -/
def typePushforward_prodLax {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P Q : Sheaf (smallEtaleTopology X) (Type u)) :
    (typePushforward f).obj P ⊗ (typePushforward f).obj Q ⟶
      (typePushforward f).obj (P ⊗ Q) :=
  (morphismOfTopoi f).adjunction.homEquiv _ _
    (CartesianMonoidalCategory.prodComparison (morphismOfTopoi f).inverseImage
        ((typePushforward f).obj P) ((typePushforward f).obj Q) ≫
      ((morphismOfTopoi f).adjunction.counit.app P ⊗ₘ
        (morphismOfTopoi f).adjunction.counit.app Q))

/-- `typePushforward_prodLax` is the adjunct of the inverse-image product comparison
followed by the tensor of counits. -/
theorem typePushforward_prodLax_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P Q : Sheaf (smallEtaleTopology X) (Type u)) :
    typePushforward_prodLax f P Q =
      (morphismOfTopoi f).adjunction.homEquiv _ _
        (CartesianMonoidalCategory.prodComparison (morphismOfTopoi f).inverseImage
            ((typePushforward f).obj P) ((typePushforward f).obj Q) ≫
          ((morphismOfTopoi f).adjunction.counit.app P ⊗ₘ
            (morphismOfTopoi f).adjunction.counit.app Q)) :=
  rfl

/-- Pointwise tensor of module presheaves over an étale commutative ring sheaf. -/
noncomputable instance etaleModulePresheaf_monoidal
    {Z : AlgebraicSpace S} (O : Sheaf (smallEtaleTopology Z) CommRingCat.{u}) :
    MonoidalCategory (PresheafOfModules.{u} (ringSheaf (smallEtaleTopology Z) O).obj) :=
  Tensor.Presheaf.monoidalCategory.{u + 1, u, u} O

/-- Sheafification of module presheaves over an étale ring sheaf is monoidal. -/
noncomputable instance moduleSheafification_monoidal
    {Z : AlgebraicSpace S} (O : Sheaf (smallEtaleTopology Z) CommRingCat.{u}) :
    (moduleSheafification.{u + 1, u, u, u} O).Monoidal :=
  Tensor.sheafificationMonoidal.{u + 1, u, u} O

/-- The sheaf tensor of étale modules is sheafification of the pointwise tensor of
underlying module presheaves. -/
noncomputable def moduleTensorSheafifyIso
    {Z : AlgebraicSpace S} (O : Sheaf (smallEtaleTopology Z) CommRingCat.{u})
    (F G : SheafOfModules.{u} (etaleRingedSite Z O).structureSheaf) :
    F ⊗ G ≅ (moduleSheafification.{u + 1, u, u, u} O).obj (F.val ⊗ G.val) :=
  tensorIso (moduleSheafificationValIso.{u + 1, u, u, u} O F).symm
      (moduleSheafificationValIso.{u + 1, u, u, u} O G).symm ≪≫
    Functor.Monoidal.μIso (moduleSheafification.{u + 1, u, u, u} O) F.val G.val

/-- `moduleTensorSheafifyIso` is the tensor of sheafification counit isomorphisms followed by
the monoidal comparison of module sheafification. -/
theorem moduleTensorSheafifyIso_eq
    {Z : AlgebraicSpace S} (O : Sheaf (smallEtaleTopology Z) CommRingCat.{u})
    (F G : SheafOfModules.{u} (etaleRingedSite Z O).structureSheaf) :
    moduleTensorSheafifyIso O F G =
      tensorIso (moduleSheafificationValIso.{u + 1, u, u, u} O F).symm
          (moduleSheafificationValIso.{u + 1, u, u, u} O G).symm ≪≫
        Functor.Monoidal.μIso (moduleSheafification.{u + 1, u, u, u} O) F.val G.val :=
  rfl

/-- The type-valued sheaf morphism sending a pair of local sections to their pure tensor. -/
noncomputable def tensorSectionUnderlying
    {Z : AlgebraicSpace S} (O : Sheaf (smallEtaleTopology Z) CommRingCat.{u})
    (F G : SheafOfModules.{u} (etaleRingedSite Z O).structureSheaf) :
    (ToInternal.underlying (etaleRingedSite Z O).structureSheaf).obj F ⊗
      (ToInternal.underlying (etaleRingedSite Z O).structureSheaf).obj G ⟶
      (ToInternal.underlying (etaleRingedSite Z O).structureSheaf).obj (F ⊗ G) :=
  let UF := (ToInternal.underlying (etaleRingedSite Z O).structureSheaf).obj F
  let UG := (ToInternal.underlying (etaleRingedSite Z O).structureSheaf).obj G
  { hom :=
      { app := fun U ↦
          ↾fun p ↦
            ((moduleTensorSheafifyIso O F G).inv.val.app U).hom
              (((moduleSheafificationUnitToVal.{u + 1, u, u, u} O (F.val ⊗ G.val)).app U).hom
                ((fst UF UG).hom.app U p ⊗ₜ (snd UF UG).hom.app U p))
        naturality := fun _ _ _ ↦ sorry } }

/-- `tensorSectionUnderlying` is natural in both module arguments. -/
theorem tensorSectionUnderlying_map
    {Z : AlgebraicSpace S} (O : Sheaf (smallEtaleTopology Z) CommRingCat.{u})
    {F F' G G' : SheafOfModules.{u} (etaleRingedSite Z O).structureSheaf}
    (f : F ⟶ F') (g : G ⟶ G') :
    ((ToInternal.underlying (etaleRingedSite Z O).structureSheaf).map f ⊗ₘ
        (ToInternal.underlying (etaleRingedSite Z O).structureSheaf).map g) ≫
      tensorSectionUnderlying O F' G' =
      tensorSectionUnderlying O F G ≫
        (ToInternal.underlying (etaleRingedSite Z O).structureSheaf).map (tensorHom f g) :=
  sorry

/-- The cartesian type-valued comparison `f_*P × f_*Q ⟶ f_*(P ⊗ Q)` transported along
`ModulePushforward.forgetIso`. -/
noncomputable def modulePushforward_tensorUnderlying {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (P Q : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    (ToInternal.underlying (etaleRingedSite Y A).structureSheaf).obj
        ((toRingedToposHom f φ).modulePushforward.obj P) ⊗
      (ToInternal.underlying (etaleRingedSite Y A).structureSheaf).obj
        ((toRingedToposHom f φ).modulePushforward.obj Q) ⟶
      (ToInternal.underlying (etaleRingedSite Y A).structureSheaf).obj
        ((toRingedToposHom f φ).modulePushforward.obj (P ⊗ Q)) :=
  ((ModulePushforward.forgetIso (toRingedToposHom f φ)).hom.app P ⊗ₘ
      (ModulePushforward.forgetIso (toRingedToposHom f φ)).hom.app Q) ≫
    typePushforward_prodLax f
        ((ToInternal.underlying (etaleRingedSite X B).structureSheaf).obj P)
        ((ToInternal.underlying (etaleRingedSite X B).structureSheaf).obj Q) ≫
      (typePushforward f).map (tensorSectionUnderlying B P Q) ≫
        (ModulePushforward.forgetIso (toRingedToposHom f φ)).inv.app (P ⊗ Q)

/-- `modulePushforward_tensorUnderlying` is the forgetful comparison followed by the
explicit lax product comparison of `typePushforward` and pushforward of
`tensorSectionUnderlying`. -/
theorem modulePushforward_tensorUnderlying_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (P Q : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    modulePushforward_tensorUnderlying f φ P Q =
      ((ModulePushforward.forgetIso (toRingedToposHom f φ)).hom.app P ⊗ₘ
          (ModulePushforward.forgetIso (toRingedToposHom f φ)).hom.app Q) ≫
        typePushforward_prodLax f
            ((ToInternal.underlying (etaleRingedSite X B).structureSheaf).obj P)
            ((ToInternal.underlying (etaleRingedSite X B).structureSheaf).obj Q) ≫
          (typePushforward f).map (tensorSectionUnderlying B P Q) ≫
            (ModulePushforward.forgetIso (toRingedToposHom f φ)).inv.app (P ⊗ Q) :=
  rfl

/-- The sectionwise bilinear map `(f_* P)(U) × (f_* Q)(U) → f_*(P ⊗ Q)(U)`. -/
noncomputable def modulePushforward_tensorBilinear {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (P Q : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    PresheafOfModules.BilinearMap A.obj
      ((toRingedToposHom f φ).modulePushforward.obj P).val
      ((toRingedToposHom f φ).modulePushforward.obj Q).val
      ((toRingedToposHom f φ).modulePushforward.obj (P ⊗ Q)).val where
  app U :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            (modulePushforward_tensorUnderlying f φ P Q).hom.app U (x, y)
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry }
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }
  naturality _ _ _ := sorry

/-- The bilinear map `modulePushforward_tensorBilinear` evaluates by the cartesian underlying
comparison. -/
theorem modulePushforward_tensorBilinear_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (P Q : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf)
    (U : (smallEtaleSite Y)ᵒᵖ)
    (x : ((toRingedToposHom f φ).modulePushforward.obj P).val.obj U)
    (y : ((toRingedToposHom f φ).modulePushforward.obj Q).val.obj U) :
    (modulePushforward_tensorBilinear f φ P Q).app U x y =
      (modulePushforward_tensorUnderlying f φ P Q).hom.app U (x, y) :=
  rfl

/-- The lax tensor comparison `f_* P ⊗ f_* Q ⟶ f_*(P ⊗ Q)` for module pushforward. -/
def modulePushforward_tensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (P Q : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    (toRingedToposHom f φ).modulePushforward.obj P ⊗
      (toRingedToposHom f φ).modulePushforward.obj Q ⟶
      (toRingedToposHom f φ).modulePushforward.obj (P ⊗ Q) :=
  (moduleTensorSheafifyIso A
      ((toRingedToposHom f φ).modulePushforward.obj P)
      ((toRingedToposHom f φ).modulePushforward.obj Q)).hom ≫
    (moduleSheafificationHomEquiv.{u + 1, u, u, u} A _ _).symm
      (modulePushforward_tensorBilinear f φ P Q).toHom

/-- `modulePushforward_tensorComparison` is sheafification of the sectionwise bilinear map. -/
theorem modulePushforward_tensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (P Q : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    modulePushforward_tensorComparison f φ P Q =
      (moduleTensorSheafifyIso A
          ((toRingedToposHom f φ).modulePushforward.obj P)
          ((toRingedToposHom f φ).modulePushforward.obj Q)).hom ≫
        (moduleSheafificationHomEquiv.{u + 1, u, u, u} A _ _).symm
          (modulePushforward_tensorBilinear f φ P Q).toHom :=
  rfl

/-- The tensor comparison `f^*(M ⊗ N) ⟶ f^* M ⊗ f^* N` for module pullback along
`toRingedToposHom f φ`, the adjunct of the tensor of units followed by the pushforward lax
comparison. -/
def modulePullbackTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (M N : SheafOfModules.{u} (etaleRingedSite Y A).structureSheaf) :
    (toRingedToposHom f φ).modulePullback.obj (M ⊗ N) ⟶
      (toRingedToposHom f φ).modulePullback.obj M ⊗
        (toRingedToposHom f φ).modulePullback.obj N :=
  ((toRingedToposHom f φ).moduleAdjunction.homEquiv _ _).symm
    (((toRingedToposHom f φ).moduleAdjunction.unit.app M ⊗ₘ
        (toRingedToposHom f φ).moduleAdjunction.unit.app N) ≫
      modulePushforward_tensorComparison f φ
        ((toRingedToposHom f φ).modulePullback.obj M)
        ((toRingedToposHom f φ).modulePullback.obj N))

/-- `modulePullbackTensorComparison` is the adjunction transpose of the tensor of the two
adjunction units. -/
theorem modulePullbackTensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (M N : SheafOfModules.{u} (etaleRingedSite Y A).structureSheaf) :
    modulePullbackTensorComparison f φ M N =
      ((toRingedToposHom f φ).moduleAdjunction.homEquiv _ _).symm
        (((toRingedToposHom f φ).moduleAdjunction.unit.app M ⊗ₘ
            (toRingedToposHom f φ).moduleAdjunction.unit.app N) ≫
          modulePushforward_tensorComparison f φ
            ((toRingedToposHom f φ).modulePullback.obj M)
            ((toRingedToposHom f φ).modulePullback.obj N)) :=
  rfl

/-- The canonical projection-formula map
`F ⊗_A f_* G ⟶ f_*(f^* F ⊗_B G)` associated to `toRingedToposHom f φ`. -/
noncomputable def projectionFormula {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (F : SheafOfModules.{u} (etaleRingedSite Y A).structureSheaf)
    (G : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    F ⊗ (toRingedToposHom f φ).modulePushforward.obj G ⟶
      (toRingedToposHom f φ).modulePushforward.obj
        ((toRingedToposHom f φ).modulePullback.obj F ⊗ G) :=
  (toRingedToposHom f φ).moduleAdjunction.projectionFormulaMateOf
    (fun M N ↦ modulePullbackTensorComparison f φ M N) F G

/-- `projectionFormula` is the right projection-formula mate of the module adjunction along the
named tensor comparison of `modulePullback`. -/
theorem projectionFormula_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (F : SheafOfModules.{u} (etaleRingedSite Y A).structureSheaf)
    (G : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    projectionFormula f φ F G =
      (toRingedToposHom f φ).moduleAdjunction.projectionFormulaMateOf
        (fun M N ↦ modulePullbackTensorComparison f φ M N) F G :=
  rfl

/-- Transposing `projectionFormula f φ F G` across the module adjunction recovers the
projection-formula map built from `modulePullbackTensorComparison` and the counit. -/
theorem projectionFormula_spec {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (φ : (etaleRingedSite Y A).structureSheaf ⟶
      (ringPushforward f).obj (etaleRingedSite X B).structureSheaf)
    (F : SheafOfModules.{u} (etaleRingedSite Y A).structureSheaf)
    (G : SheafOfModules.{u} (etaleRingedSite X B).structureSheaf) :
    ((toRingedToposHom f φ).moduleAdjunction.homEquiv _ _).symm
        (projectionFormula f φ F G) =
      modulePullbackTensorComparison f φ F
          ((toRingedToposHom f φ).modulePushforward.obj G) ≫
        (𝟙 _ ⊗ₘ (toRingedToposHom f φ).moduleAdjunction.counit.app G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
