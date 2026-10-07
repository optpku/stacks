module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import stacks_project.Chap96.Lemma_96_11_4_Comparison
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh
public import stacks_project.Chap96.Lemma_96_12_5_AssociatedModules

/-!
# Topology comparison for quasi-coherent modules on groupoid fibrations

Identity-on-Γ restriction of scalars transports quasi-coherent modules on a
category fibred in groupoids between the associated Zariski, étale, and fppf
sites, and into the étale locally quasi-coherent category.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
  CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty Opposite
  SheafOfModules SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Identity-on-Γ comparison of the associated `τ`-structure presheaf with the
underlying ring presheaf of the commutative associated structure sheaf. -/
def associatedToCommStructurePresheafIso (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedStructureSheaf X τ).obj ≅
      (commAssociatedStructureSheaf X τ).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u} :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (X.associatedTopology τ) (τ.overTopology S)).app
    (StandardTopology.Big.structureSheaf τ S) ≪≫
    isoWhiskerLeft X.p.op
      (associator (Over.forget S).op Scheme.Γ
        (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    (associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
      (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    (isoWhiskerRight
      ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
          (X.associatedTopology τ) (τ.overTopology S)).app
        (bigCommStructureSheaf τ))
      (forget₂ CommRingCat.{u} RingCat.{u})).symm

/-- `associatedToCommStructurePresheafIso` is the composite of the continuous
pushforward identifications with the associator for `Γ ⋙ forget₂`. -/
theorem associatedToCommStructurePresheafIso_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    associatedToCommStructurePresheafIso X τ =
      (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
          (X.associatedTopology τ) (τ.overTopology S)).app
        (StandardTopology.Big.structureSheaf τ S) ≪≫
        isoWhiskerLeft X.p.op
          (associator (Over.forget S).op Scheme.Γ
            (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
        (associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
          (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
        (isoWhiskerRight
          ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
              (X.associatedTopology τ) (τ.overTopology S)).app
            (bigCommStructureSheaf τ))
          (forget₂ CommRingCat.{u} RingCat.{u})).symm :=
  sorry

/-- Transport of fppf `𝒪_X`-modules to the associated `τ`-site by
identity-on-Γ restriction of scalars. -/
def toAssociatedModules (X : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤ associatedModules X τ where
  obj F :=
    { val := toAssociatedPresheaf F.val τ
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars
          (associatedToFppfStructurePresheaf X τ)).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `toAssociatedModules` is `toAssociatedPresheaf` on
underlying module presheaves. -/
theorem toAssociatedModules_obj (X : GroupoidsOver S) (τ : StandardTopology)
    (F : RingedSite.ModuleCat.{u} (fppfRingedSite X)) :
    ((toAssociatedModules X τ).obj F).val = toAssociatedPresheaf F.val τ :=
  sorry

/-- The coefficient morphism from the commutative associated `τ`-structure
presheaf to the fppf structure presheaf. -/
def toCommAssociatedCoefficient (X : GroupoidsOver S) (τ : StandardTopology) :
    ((commAssociatedStructureSheaf X τ).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      (structureSheaf X).obj :=
  (associatedToCommStructurePresheafIso X τ).inv ≫
    associatedToFppfStructurePresheaf X τ

/-- `toCommAssociatedCoefficient` is the inverse associated-to-commutative
identification followed by `associatedToFppfStructurePresheaf`. -/
theorem toCommAssociatedCoefficient_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    toCommAssociatedCoefficient X τ =
      (associatedToCommStructurePresheafIso X τ).inv ≫
        associatedToFppfStructurePresheaf X τ :=
  sorry

/-- The coefficient morphism from the fppf structure presheaf to the commutative
associated `τ`-structure presheaf. -/
def fromCommAssociatedCoefficient (X : GroupoidsOver S) (τ : StandardTopology) :
    (structureSheaf X).obj ⟶
      ((commAssociatedStructureSheaf X τ).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}) :=
  (associatedStructurePresheafIso X τ).hom ≫
    (associatedToCommStructurePresheafIso X τ).hom

/-- `fromCommAssociatedCoefficient` is the associated-structure identification
followed by the commutative presentation identification. -/
theorem fromCommAssociatedCoefficient_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    fromCommAssociatedCoefficient X τ =
      (associatedStructurePresheafIso X τ).hom ≫
        (associatedToCommStructurePresheafIso X τ).hom :=
  sorry

/-- The two coefficient morphisms compose to the identity of the fppf structure
presheaf. -/
theorem fromCommAssociatedCoefficient_comp_toCommAssociatedCoefficient
    (X : GroupoidsOver S) (τ : StandardTopology) :
    fromCommAssociatedCoefficient X τ ≫ toCommAssociatedCoefficient X τ =
      𝟙 (structureSheaf X).obj :=
  sorry

/-- The two coefficient morphisms compose to the identity of the commutative
associated structure presheaf. -/
theorem toCommAssociatedCoefficient_comp_fromCommAssociatedCoefficient
    (X : GroupoidsOver S) (τ : StandardTopology) :
    toCommAssociatedCoefficient X τ ≫ fromCommAssociatedCoefficient X τ =
      𝟙 ((commAssociatedStructureSheaf X τ).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Transport of fppf `𝒪_X`-modules to the commutative associated `τ`-site. -/
def toCommAssociatedModules (X : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤
      commAssociatedModules X τ where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars
          (toCommAssociatedCoefficient X τ)).obj F.val
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars
          (toCommAssociatedCoefficient X τ)).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `toCommAssociatedModules` is restriction of scalars
along `toCommAssociatedCoefficient`. -/
theorem toCommAssociatedModules_obj (X : GroupoidsOver S) (τ : StandardTopology)
    (F : RingedSite.ModuleCat.{u} (fppfRingedSite X)) :
    ((toCommAssociatedModules X τ).obj F).val =
      (PresheafOfModules.restrictScalars
        (toCommAssociatedCoefficient X τ)).obj F.val :=
  sorry

/-- Identity-on-Γ transport of the commutative fppf presentation back to fppf modules. -/
def fromCommAssociatedModules (X : GroupoidsOver S) :
    commAssociatedModules X .fppf ⥤
      RingedSite.ModuleCat.{u} (fppfRingedSite X) where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fromCommAssociatedCoefficient X .fppf)).obj F.val
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fromCommAssociatedCoefficient X .fppf)).map f.val }
  map_id := sorry
  map_comp := sorry

/-- Transport of fppf `𝒪_X`-modules to étale `𝒪_X`-modules by identity-on-Γ
restriction of scalars. -/
def toEtaleModules (X : GroupoidsOver S) :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤ etaleModules X where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fppfToEtaleStructurePresheafIso X).inv).obj F.val
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars
          (fppfToEtaleStructurePresheafIso X).inv).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `toEtaleModules` is restriction of scalars along the
inverse of `fppfToEtaleStructurePresheafIso`. -/
theorem toEtaleModules_obj (X : GroupoidsOver S)
    (F : RingedSite.ModuleCat.{u} (fppfRingedSite X)) :
    ((toEtaleModules X).obj F).val =
      (PresheafOfModules.restrictScalars
        (fppfToEtaleStructurePresheafIso X).inv).obj F.val :=
  sorry

/-- Identity-on-Γ identification of the commutative associated `τ`-structure
presheaf with `p.op ⋙ Γ`. -/
def commAssociatedToGamma (X : GroupoidsOver S) (τ : StandardTopology) :
    (commAssociatedStructureSheaf X τ).obj ≅
      X.p.op ⋙ (Over.forget S).op ⋙ Scheme.Γ :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
      (X.associatedTopology τ) (τ.overTopology S)).app
    (bigCommStructureSheaf τ)

/-- `commAssociatedToGamma` is the continuous pushforward identification of the
big commutative structure sheaf. -/
theorem commAssociatedToGamma_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    commAssociatedToGamma X τ =
      (X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
          (X.associatedTopology τ) (τ.overTopology S)).app
        (bigCommStructureSheaf τ) :=
  sorry

/-- Coefficient morphism of commutative associated structure presheaves,
identity on global sections. -/
def commAssociatedCoefficient (X : GroupoidsOver S)
    (τ σ : StandardTopology) :
    (commAssociatedStructureSheaf X τ).obj ⟶
      (commAssociatedStructureSheaf X σ).obj :=
  (commAssociatedToGamma X τ).hom ≫ (commAssociatedToGamma X σ).inv

/-- `commAssociatedCoefficient` is the composite of the `Γ`-identifications. -/
theorem commAssociatedCoefficient_eq (X : GroupoidsOver S)
    (τ σ : StandardTopology) :
    commAssociatedCoefficient X τ σ =
      (commAssociatedToGamma X τ).hom ≫ (commAssociatedToGamma X σ).inv :=
  sorry

/-- Identity-on-Γ coefficients from associated `τ` to fppf factor through the
commutative associated coefficient. -/
theorem toCommAssociatedCoefficient_eq_comp (X : GroupoidsOver S)
    (τ : StandardTopology) :
    toCommAssociatedCoefficient X τ =
      PresheafOfModules.presheafStructureMap
          (commAssociatedCoefficient X τ .fppf) ≫
        toCommAssociatedCoefficient X .fppf :=
  sorry

/-- Identity-on-Γ coefficients from fppf to associated `τ` factor through the
commutative associated coefficient. -/
theorem fromCommAssociatedCoefficient_eq_comp (X : GroupoidsOver S)
    (τ : StandardTopology) :
    fromCommAssociatedCoefficient X τ =
      fromCommAssociatedCoefficient X .fppf ≫
        PresheafOfModules.presheafStructureMap
          (commAssociatedCoefficient X .fppf τ) :=
  sorry

/-- The big commutative étale structure sheaf of `S` agrees with the associated
étale presentation of `bigCommStructureSheaf`. -/
def bigCommStructureSheaf_etaleIso :
    bigCommStructureSheaf (S := S) .etale ≅ bigEtaleCommStructureSheaf (S := S) where
  hom := Sheaf.homEquiv.symm (𝟙 _)
  inv := Sheaf.homEquiv.symm (𝟙 _)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The commutative associated étale structure sheaf of `X` agrees with
`commEtaleStructureSheaf`. -/
def commAssociatedToEtaleStructureSheafIso (X : GroupoidsOver S) :
    commAssociatedStructureSheaf X .etale ≅ commEtaleStructureSheaf X :=
  (X.p.sheafPushforwardContinuous CommRingCat.{u}
      (X.associatedTopology .etale) (StandardTopology.etale.overTopology S)).mapIso
    bigCommStructureSheaf_etaleIso

/-- The underlying ring sheaves of `commAssociatedRingedSite X .etale` and
`etaleRingedSite X` are isomorphic by identity-on-Γ. -/
def commAssociatedToEtaleRingSheafIso (X : GroupoidsOver S) :
    (commAssociatedRingedSite X .etale).structureSheaf ≅
      (etaleRingedSite X).structureSheaf :=
  (sheafCompose (X.associatedTopology .etale)
      (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    (commAssociatedToEtaleStructureSheafIso X)

/-- Restriction of scalars along `commAssociatedToEtaleRingSheafIso` identifies
commutative associated étale modules with `etaleModules`. -/
def commAssociatedModules_etaleEquivalence (X : GroupoidsOver S) :
    commAssociatedModules X .etale ≌ etaleModules X :=
  SheafOfModules.Restriction.equivalenceOfIso
    (commAssociatedToEtaleRingSheafIso X)


/-- Identity-on-Γ restriction of fppf module sheaves to an associated coarser topology. -/
def restrictCommAssociatedModules (X : GroupoidsOver S) (τ σ : StandardTopology) (hσ : σ = .fppf) :
    commAssociatedModules X σ ⥤ commAssociatedModules X τ where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap
            (commAssociatedCoefficient X τ σ))).obj F.val
      isSheaf := by
        subst σ
        exact sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap
            (commAssociatedCoefficient X τ σ))).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `restrictCommAssociatedModules` is restriction of
scalars along `commAssociatedCoefficient`. -/
theorem restrictCommAssociatedModules_obj (X : GroupoidsOver S)
    (τ σ : StandardTopology) (hσ : σ = .fppf) (F : commAssociatedModules X σ) :
    ((restrictCommAssociatedModules X τ σ hσ).obj F).val =
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap
          (commAssociatedCoefficient X τ σ))).obj F.val :=
  sorry


/-- Tensor product of commutative associated modules, computed in the module
category as the sheafification of the pointwise tensor. -/
def associatedModuleTensor {X : GroupoidsOver S} {τ : StandardTopology}
    (F G : commAssociatedModules X τ) : commAssociatedModules X τ :=
  (moduleSheafification.{u + 1, u, u, u} (commAssociatedStructureSheaf X τ)).obj
    (PresheafOfModules.Monoidal.tensorObj F.val G.val)

/-- The morphism of associated module tensors induced by a pair of module
morphisms. -/
def associatedModuleTensorMap {X : GroupoidsOver S} {τ : StandardTopology}
    {F₁ F₂ G₁ G₂ : commAssociatedModules X τ} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    associatedModuleTensor F₁ G₁ ⟶ associatedModuleTensor F₂ G₂ :=
  (moduleSheafification.{u + 1, u, u, u} (commAssociatedStructureSheaf X τ)).map
    (PresheafOfModules.Monoidal.tensorHom f.val g.val)

/-- The sheafified pointwise tensor is canonically isomorphic to the monoidal
tensor product in `Mod(X_τ, 𝒪_X)`. -/
noncomputable def associatedModuleTensorIso {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    associatedModuleTensor F G ≅ moduleTensorAssociated F G :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u}
        (commAssociatedStructureSheaf X τ)) F.val G.val).symm ≪≫
    tensorIso
      (moduleSheafificationValIso.{u + 1, u, u, u}
        (commAssociatedStructureSheaf X τ) F)
      (moduleSheafificationValIso.{u + 1, u, u, u}
        (commAssociatedStructureSheaf X τ) G)

/-- `associatedModuleTensorIso` identifies sheafified pointwise tensors with
`moduleTensorAssociated`. -/
theorem associatedModuleTensorIso_eq {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    associatedModuleTensorIso F G =
      (Functor.Monoidal.μIso
          (moduleSheafification.{u + 1, u, u, u}
            (commAssociatedStructureSheaf X τ)) F.val G.val).symm ≪≫
        tensorIso
          (moduleSheafificationValIso.{u + 1, u, u, u}
            (commAssociatedStructureSheaf X τ) F)
          (moduleSheafificationValIso.{u + 1, u, u, u}
            (commAssociatedStructureSheaf X τ) G) :=
  sorry

/-- A presheaf morphism into a restricted target descends to sheafifications of
commutative associated modules. -/
def associatedMapToRestriction {X : GroupoidsOver S} {τ σ : StandardTopology} (hσ : σ = .fppf)
    {P : PresheafOfModules.{u}
      (CategoryTheory.Sheaf.ringSheafOfComm
        (commAssociatedStructureSheaf X τ)).obj}
    {Q : PresheafOfModules.{u}
      (CategoryTheory.Sheaf.ringSheafOfComm
        (commAssociatedStructureSheaf X σ)).obj}
    (f : P ⟶
      (PresheafOfModules.restrictScalars.{u}
        (PresheafOfModules.presheafStructureMap
          (commAssociatedCoefficient X τ σ))).obj Q) :
    (moduleSheafification.{u + 1, u, u, u}
        (commAssociatedStructureSheaf X τ)).obj P ⟶
      (restrictCommAssociatedModules X τ σ hσ).obj
        ((moduleSheafification.{u + 1, u, u, u} (commAssociatedStructureSheaf X σ)).obj Q) :=
  (moduleSheafificationHomEquiv.{u + 1, u, u, u}
      (commAssociatedStructureSheaf X τ) P
      ((restrictCommAssociatedModules X τ σ hσ).obj
        ((moduleSheafification.{u + 1, u, u, u} (commAssociatedStructureSheaf X σ)).obj Q))).symm
    (f ≫
      (PresheafOfModules.restrictScalars.{u}
        (PresheafOfModules.presheafStructureMap
          (commAssociatedCoefficient X τ σ))).map
        (moduleSheafificationUnitToVal.{u + 1, u, u, u} (commAssociatedStructureSheaf X σ) Q))


/-- The universe lift of one value of a commutative associated module. -/
noncomputable abbrev commAssociatedModuleLiftObj {X : GroupoidsOver S}
    {τ : StandardTopology} (M : commAssociatedModules X τ) (U : X.totalᵒᵖ) :
    ModuleCat.{u + 1} ((commAssociatedStructureSheafLift X τ).obj.obj U) :=
  (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
    ((ModuleCat.uliftFunctor.{u + 1, u}
      ((CategoryTheory.Sheaf.ringSheafOfComm
        (commAssociatedStructureSheaf X τ)).obj.obj U)).obj (M.val.obj U))

/-- The universe-lifted action of a module morphism preserves addition. -/
theorem commAssociatedModuleLiftMap_add {X : GroupoidsOver S}
    {τ : StandardTopology} {M N : commAssociatedModules X τ} (f : M ⟶ N)
    (U : X.totalᵒᵖ) (x y : commAssociatedModuleLiftObj M U) :
    ULift.up (f.val.app U (x + y).down) =
      ULift.up (f.val.app U x.down) + ULift.up (f.val.app U y.down) :=
  sorry

/-- The universe-lifted action of a module morphism preserves scalar
multiplication. -/
theorem commAssociatedModuleLiftMap_smul {X : GroupoidsOver S}
    {τ : StandardTopology} {M N : commAssociatedModules X τ} (f : M ⟶ N)
    (U : X.totalᵒᵖ) (r : (commAssociatedStructureSheafLift X τ).obj.obj U)
    (x : commAssociatedModuleLiftObj M U) :
    (ULift.up (f.val.app U (r • x).down) : commAssociatedModuleLiftObj N U) =
      @SMul.smul ((commAssociatedStructureSheafLift X τ).obj.obj U)
        (commAssociatedModuleLiftObj N U)
        (ModuleCat.isModule (commAssociatedModuleLiftObj N U)).toSMul r
        (ULift.up (f.val.app U x.down)) :=
  sorry

/-- The universe lift of a component of a morphism of commutative associated
modules. -/
noncomputable def commAssociatedModuleLiftMap {X : GroupoidsOver S}
    {τ : StandardTopology} {M N : commAssociatedModules X τ} (f : M ⟶ N)
    (U : X.totalᵒᵖ) :
    commAssociatedModuleLiftObj M U ⟶ commAssociatedModuleLiftObj N U :=
  let source : ModuleCat.{u + 1}
      ((commAssociatedStructureSheafLift X τ).obj.obj U) :=
    commAssociatedModuleLiftObj M U
  let target : ModuleCat.{u + 1}
      ((commAssociatedStructureSheafLift X τ).obj.obj U) :=
    commAssociatedModuleLiftObj N U
  @ModuleCat.ofHom ((commAssociatedStructureSheafLift X τ).obj.obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (f.val.app U x.down)
      map_add' := commAssociatedModuleLiftMap_add f U
      map_smul' := commAssociatedModuleLiftMap_smul f U }

/-- The scalar-restricted target of a lifted restriction map. -/
noncomputable abbrev commAssociatedModuleLiftRestrictionTarget
    {X : GroupoidsOver S} {τ : StandardTopology}
    (M : commAssociatedModules X τ) {U V : X.totalᵒᵖ} (i : U ⟶ V) :=
  (ModuleCat.restrictScalars
    ((commAssociatedStructureSheafLift X τ).obj.map i).hom).obj
    (commAssociatedModuleLiftObj M V)

/-- A lifted restriction map preserves addition. -/
theorem commAssociatedModuleLiftRestrictionMap_add {X : GroupoidsOver S}
    {τ : StandardTopology} (M : commAssociatedModules X τ)
    {U V : X.totalᵒᵖ} (i : U ⟶ V)
    (x y : commAssociatedModuleLiftObj M U) :
    (ULift.up (M.val.map i (x + y).down) :
        commAssociatedModuleLiftRestrictionTarget M i) =
      ULift.up (M.val.map i x.down) + ULift.up (M.val.map i y.down) :=
  sorry

/-- A lifted restriction map preserves scalar multiplication. -/
theorem commAssociatedModuleLiftRestrictionMap_smul {X : GroupoidsOver S}
    {τ : StandardTopology} (M : commAssociatedModules X τ)
    {U V : X.totalᵒᵖ} (i : U ⟶ V)
    (r : (commAssociatedStructureSheafLift X τ).obj.obj U)
    (x : commAssociatedModuleLiftObj M U) :
    (ULift.up (M.val.map i (r • x).down) :
        commAssociatedModuleLiftRestrictionTarget M i) =
      @SMul.smul ((commAssociatedStructureSheafLift X τ).obj.obj U)
        (commAssociatedModuleLiftRestrictionTarget M i)
        (ModuleCat.isModule
          (commAssociatedModuleLiftRestrictionTarget M i)).toSMul r
        (ULift.up (M.val.map i x.down)) :=
  sorry

/-- The universe lift of a restriction map of a commutative associated module. -/
noncomputable def commAssociatedModuleLiftRestrictionMap {X : GroupoidsOver S}
    {τ : StandardTopology} (M : commAssociatedModules X τ)
    {U V : X.totalᵒᵖ} (i : U ⟶ V) :
    commAssociatedModuleLiftObj M U ⟶
      commAssociatedModuleLiftRestrictionTarget M i :=
  let source : ModuleCat.{u + 1}
      ((commAssociatedStructureSheafLift X τ).obj.obj U) :=
    commAssociatedModuleLiftObj M U
  let target : ModuleCat.{u + 1}
      ((commAssociatedStructureSheafLift X τ).obj.obj U) :=
    commAssociatedModuleLiftRestrictionTarget M i
  @ModuleCat.ofHom ((commAssociatedStructureSheafLift X τ).obj.obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (M.val.map i x.down)
      map_add' := commAssociatedModuleLiftRestrictionMap_add M i
      map_smul' := commAssociatedModuleLiftRestrictionMap_smul M i }

/-- The universe lift of the underlying presheaf of a commutative associated
module. -/
noncomputable def commAssociatedModuleLiftPresheaf {X : GroupoidsOver S}
    {τ : StandardTopology} (M : commAssociatedModules X τ) :
    PresheafOfModules.{u + 1}
      (CategoryTheory.Sheaf.ringSheafOfComm
        (commAssociatedStructureSheafLift X τ)).obj where
  obj U := commAssociatedModuleLiftObj M U
  map i := commAssociatedModuleLiftRestrictionMap M i
  map_id := sorry
  map_comp := sorry

/-- Universe lifting preserves the sheaf condition on an associated `τ`-site. -/
theorem commAssociatedModuleLiftPresheaf_isSheaf {X : GroupoidsOver S}
    {τ : StandardTopology} (M : commAssociatedModules X τ) :
    Presheaf.IsSheaf (X.associatedTopology τ)
      (commAssociatedModuleLiftPresheaf M).presheaf :=
  sorry

/-- The universe lift of a morphism of commutative associated modules. -/
noncomputable def commAssociatedModuleLiftNatTrans {X : GroupoidsOver S}
    {τ : StandardTopology} {M N : commAssociatedModules X τ} (f : M ⟶ N) :
    commAssociatedModuleLiftPresheaf M ⟶ commAssociatedModuleLiftPresheaf N where
  app U := commAssociatedModuleLiftMap f U
  naturality := sorry

/-- The functorial universe lift from commutative associated modules to their
universe-`u + 1` presentation. -/
noncomputable def commAssociatedModulesLiftFunctor (X : GroupoidsOver S)
    (τ : StandardTopology) :
    commAssociatedModules X τ ⥤ commAssociatedModulesLift X τ where
  obj M :=
    ⟨commAssociatedModuleLiftPresheaf M,
      commAssociatedModuleLiftPresheaf_isSheaf M⟩
  map f := ⟨commAssociatedModuleLiftNatTrans f⟩
  map_id := sorry
  map_comp := sorry

namespace QCoh

/-- Transport of quasi-coherent modules to the associated `τ`-module category. -/
def toAssociatedModules (X : GroupoidsOver S) (τ : StandardTopology) :
    QCoh X ⥤ associatedModules X τ :=
  (quasiCoherentModuleProperty X).ι ⋙ GroupoidsOver.toAssociatedModules X τ

/-- `QCoh.toAssociatedModules` is the inclusion into fppf modules followed by
`toAssociatedModules`. -/
theorem toAssociatedModules_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    toAssociatedModules X τ =
      (quasiCoherentModuleProperty X).ι ⋙ GroupoidsOver.toAssociatedModules X τ :=
  sorry

/-- The object action of `QCoh.toAssociatedModules`. -/
theorem toAssociatedModules_obj (X : GroupoidsOver S) (τ : StandardTopology)
    (F : QCoh X) :
    (toAssociatedModules X τ).obj F =
      (GroupoidsOver.toAssociatedModules X τ).obj F.obj :=
  sorry

/-- Transport of quasi-coherent modules to the commutative associated `τ`-module
category. -/
def toCommAssociatedModules (X : GroupoidsOver S) (τ : StandardTopology) :
    QCoh X ⥤ commAssociatedModules X τ :=
  (quasiCoherentModuleProperty X).ι ⋙ GroupoidsOver.toCommAssociatedModules X τ

/-- `QCoh.toCommAssociatedModules` is the inclusion followed by
`toCommAssociatedModules`. -/
theorem toCommAssociatedModules_eq (X : GroupoidsOver S)
    (τ : StandardTopology) :
    toCommAssociatedModules X τ =
      (quasiCoherentModuleProperty X).ι ⋙ GroupoidsOver.toCommAssociatedModules X τ :=
  sorry

/-- Transport of quasi-coherent modules to étale `𝒪_X`-modules. -/
def toEtaleModules (X : GroupoidsOver S) : QCoh X ⥤ etaleModules X :=
  (quasiCoherentModuleProperty X).ι ⋙ GroupoidsOver.toEtaleModules X

/-- `QCoh.toEtaleModules` is the inclusion followed by `toEtaleModules`. -/
theorem toEtaleModules_eq (X : GroupoidsOver S) :
    toEtaleModules X = (quasiCoherentModuleProperty X).ι ⋙ GroupoidsOver.toEtaleModules X :=
  sorry

/-- Transport of quasi-coherent modules into locally quasi-coherent étale
modules. -/
def toLQCoh (X : GroupoidsOver S) : QCoh X ⥤ LQCoh X where
  obj F := ⟨(toEtaleModules X).obj F, sorry⟩
  map f := homMk ((toEtaleModules X).map f)
  map_id := sorry
  map_comp := sorry

/-- The inclusion of `LQCoh` recovers étale transport of a quasi-coherent
module. -/
theorem toLQCoh_comp_inclusion (X : GroupoidsOver S) :
    toLQCoh X ⋙ LQCoh.inclusion X = toEtaleModules X :=
  sorry

/-- `toAssociatedModules` preserves colimits of diagrams computed in the
associated Zariski module category. -/
instance toAssociatedModules_preservesColimitsOfShape_zariski
    (X : GroupoidsOver S) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toAssociatedModules X .zariski) :=
  sorry

/-- `toAssociatedModules` preserves colimits of diagrams computed in the
associated étale module category. -/
instance toAssociatedModules_preservesColimitsOfShape_etale
    (X : GroupoidsOver S) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toAssociatedModules X .etale) :=
  sorry

/-- `toAssociatedModules` preserves colimits of diagrams computed in the
associated fppf module category. -/
instance toAssociatedModules_preservesColimitsOfShape_fppf
    (X : GroupoidsOver S) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toAssociatedModules X .fppf) :=
  sorry

/-- `toEtaleModules` preserves colimits of every universe-compatible shape. -/
instance toEtaleModules_preservesColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toEtaleModules X) :=
  sorry

/-- `toLQCoh` preserves colimits of every universe-compatible shape. -/
instance toLQCoh_preservesColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (toLQCoh X) :=
  sorry

/-- Wrap a module-presheaf morphism as a morphism of associated module sheaves. -/
def sheafHomOfVal {X : GroupoidsOver S} {τ : StandardTopology}
    {M N : commAssociatedModules X τ} (f : M.val ⟶ N.val) : M ⟶ N :=
  ⟨f⟩

/-- Wrap a module-presheaf isomorphism as an isomorphism of associated module
sheaves. -/
def sheafIsoOfValIso {X : GroupoidsOver S} {τ : StandardTopology}
    {M N : commAssociatedModules X τ} (e : M.val ≅ N.val) : M ≅ N where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-Γ identifies associated `τ`-modules with the restriction of the
commutative fppf presentation. -/
def toCommAssociatedModules_restrictIso {X : GroupoidsOver S}
    (τ : StandardTopology) (F : QCoh X) :
    (toCommAssociatedModules X τ).obj F ≅
      (restrictCommAssociatedModules X τ .fppf rfl).obj
        ((toCommAssociatedModules X .fppf).obj F) :=
  sheafIsoOfValIso
    (PresheafOfModules.Restriction.compComponentIso'
      (PresheafOfModules.presheafStructureMap
        (commAssociatedCoefficient X τ .fppf))
      (toCommAssociatedCoefficient X .fppf)
      (toCommAssociatedCoefficient X τ)
      (toCommAssociatedCoefficient_eq_comp X τ) F.obj.val)

/-- Identity-on-Γ restriction of scalars recovers a commutative fppf module. -/
def toFromCommAssociatedModulesIso {X : GroupoidsOver S}
    (M : commAssociatedModules X .fppf) :
    (GroupoidsOver.toCommAssociatedModules X .fppf).obj
        ((fromCommAssociatedModules X).obj M) ≅ M :=
  sheafIsoOfValIso
    (PresheafOfModules.Restriction.compComponentIso'
        (toCommAssociatedCoefficient X .fppf)
        (fromCommAssociatedCoefficient X .fppf)
        (𝟙 ((commAssociatedStructureSheaf X .fppf).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u}))
        (toCommAssociatedCoefficient_comp_fromCommAssociatedCoefficient X .fppf)
        M.val ≪≫
      (PresheafOfModules.Restriction.idComponentIso'
        (𝟙 ((commAssociatedStructureSheaf X .fppf).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u})) rfl M.val).symm)

/-- The common quasi-coherent tensor product, computed as the module-category
tensor on the commutative fppf presentation and transported back to `QCoh`. -/
def quasicoherentTensor {X : GroupoidsOver S} (F G : QCoh X) : QCoh X where
  obj :=
    (fromCommAssociatedModules X).obj
      (moduleTensorAssociated
        ((toCommAssociatedModules X .fppf).obj F)
        ((toCommAssociatedModules X .fppf).obj G))
  property := sorry

/-- The underlying fppf module of `quasicoherentTensor` is the transport of the
commutative fppf module tensor. -/
theorem quasicoherentTensor_obj {X : GroupoidsOver S} (F G : QCoh X) :
    (quasicoherentTensor F G).obj =
      (fromCommAssociatedModules X).obj
        (moduleTensorAssociated
          ((toCommAssociatedModules X .fppf).obj F)
          ((toCommAssociatedModules X .fppf).obj G)) :=
  sorry

/-- Identity-on-Γ tensor comparison on restricted commutative fppf presentations,
built from restriction-of-scalars tensor comparison and the sheafification unit
of the module monoidal structure, transported along
`associatedModuleTensorIso`. -/
def tensorComparison_restrict {X : GroupoidsOver S} (τ : StandardTopology)
    (F G : QCoh X) :
    moduleTensorAssociated
        ((restrictCommAssociatedModules X τ .fppf rfl).obj
          ((toCommAssociatedModules X StandardTopology.fppf).obj F))
        ((restrictCommAssociatedModules X τ .fppf rfl).obj
          ((toCommAssociatedModules X StandardTopology.fppf).obj G)) ⟶
      (restrictCommAssociatedModules X τ .fppf rfl).obj
        (moduleTensorAssociated
          ((toCommAssociatedModules X StandardTopology.fppf).obj F)
          ((toCommAssociatedModules X StandardTopology.fppf).obj G)) :=
  (associatedModuleTensorIso
      ((restrictCommAssociatedModules X τ .fppf rfl).obj
        ((toCommAssociatedModules X StandardTopology.fppf).obj F))
      ((restrictCommAssociatedModules X τ .fppf rfl).obj
        ((toCommAssociatedModules X StandardTopology.fppf).obj G))).inv ≫
    associatedMapToRestriction rfl
      (PresheafOfModules.Restriction.tensorComparison
        (commAssociatedCoefficient X τ StandardTopology.fppf)
        ((toCommAssociatedModules X StandardTopology.fppf).obj F).val
        ((toCommAssociatedModules X StandardTopology.fppf).obj G).val) ≫
    (restrictCommAssociatedModules X τ .fppf rfl).map
      (associatedModuleTensorIso
        ((toCommAssociatedModules X StandardTopology.fppf).obj F)
        ((toCommAssociatedModules X StandardTopology.fppf).obj G)).hom

/-- Canonical comparison in `commAssociatedModules X τ` from the tensor product
computed on the associated `τ`-site to the identity-on-Γ transport of the
common fppf tensor. -/
def tensorComparison {X : GroupoidsOver S} (τ : StandardTopology)
    (F G : QCoh X) :
    moduleTensorAssociated ((toCommAssociatedModules X τ).obj F)
      ((toCommAssociatedModules X τ).obj G) ⟶
      (toCommAssociatedModules X τ).obj (quasicoherentTensor F G) :=
  SheafOfModules.RingedSite.moduleTensorMap.{u + 1, u, u}
      (toCommAssociatedModules_restrictIso τ F).hom
      (toCommAssociatedModules_restrictIso τ G).hom ≫
    tensorComparison_restrict τ F G ≫
    (restrictCommAssociatedModules X τ .fppf rfl).map
      (toFromCommAssociatedModulesIso
        (moduleTensorAssociated
          ((toCommAssociatedModules X StandardTopology.fppf).obj F)
          ((toCommAssociatedModules X StandardTopology.fppf).obj G))).inv ≫
    (toCommAssociatedModules_restrictIso τ (quasicoherentTensor F G)).inv

/-- Finite local freeness of a quasi-coherent module may be tested on the
underlying fppf module, or on the associated Zariski, étale, or fppf site. -/
theorem finiteLocallyFree_tfae {X : GroupoidsOver S} (F : QCoh X) :
    List.TFAE
      [SheafOfModules.IsFiniteLocallyFree F.obj,
        SheafOfModules.IsFiniteLocallyFree
          ((toAssociatedModules X .zariski).obj F),
        SheafOfModules.IsFiniteLocallyFree
          ((toAssociatedModules X .etale).obj F),
        SheafOfModules.IsFiniteLocallyFree
          ((toAssociatedModules X .fppf).obj F)] :=
  sorry

/-- Finite local freeness of the underlying fppf module is equivalent to finite
local freeness on the associated Zariski site. -/
theorem isFiniteLocallyFree_obj_iff_zariski {X : GroupoidsOver S}
    (F : QCoh X) :
    SheafOfModules.IsFiniteLocallyFree F.obj ↔
      SheafOfModules.IsFiniteLocallyFree
        ((toAssociatedModules X .zariski).obj F) :=
  sorry

/-- Finite local freeness of the underlying fppf module is equivalent to finite
local freeness on the associated étale site. -/
theorem isFiniteLocallyFree_obj_iff_etale {X : GroupoidsOver S}
    (F : QCoh X) :
    SheafOfModules.IsFiniteLocallyFree F.obj ↔
      SheafOfModules.IsFiniteLocallyFree
        ((toAssociatedModules X .etale).obj F) :=
  sorry

/-- Finite local freeness of the underlying fppf module is equivalent to finite
local freeness on the associated fppf site. -/
theorem isFiniteLocallyFree_obj_iff_fppf {X : GroupoidsOver S}
    (F : QCoh X) :
    SheafOfModules.IsFiniteLocallyFree F.obj ↔
      SheafOfModules.IsFiniteLocallyFree
        ((toAssociatedModules X .fppf).obj F) :=
  sorry

/-- Finite local freeness on the associated Zariski site is equivalent to
finite local freeness on the associated étale site. -/
theorem isFiniteLocallyFree_zariski_iff_etale {X : GroupoidsOver S}
    (F : QCoh X) :
    SheafOfModules.IsFiniteLocallyFree
        ((toAssociatedModules X .zariski).obj F) ↔
      SheafOfModules.IsFiniteLocallyFree
        ((toAssociatedModules X .etale).obj F) :=
  sorry

/-- Finite local freeness on the associated étale site is equivalent to finite
local freeness on the associated fppf site. -/
theorem isFiniteLocallyFree_etale_iff_fppf {X : GroupoidsOver S} (F : QCoh X) :
    SheafOfModules.IsFiniteLocallyFree
        ((toAssociatedModules X .etale).obj F) ↔
      SheafOfModules.IsFiniteLocallyFree
        ((toAssociatedModules X .fppf).obj F) :=
  sorry

/-- Restriction of scalars along identity-on-Γ preserves finite local
freeness of commutative associated modules. -/
instance restrictCommAssociatedModules_isFiniteLocallyFree
    {X : GroupoidsOver S} {τ : StandardTopology}
    (F : commAssociatedModules X .fppf)
    [SheafOfModules.IsFiniteLocallyFree F] :
    SheafOfModules.IsFiniteLocallyFree
      ((restrictCommAssociatedModules X τ .fppf rfl).obj F) :=
  sorry

/-- Identity-on-Γ transport of a finite locally free quasi-coherent module
remains finite locally free. -/
instance toCommAssociatedModules_isFiniteLocallyFree
    {X : GroupoidsOver S} {τ : StandardTopology} (F : QCoh X)
    [SheafOfModules.IsFiniteLocallyFree F.obj] :
    SheafOfModules.IsFiniteLocallyFree
      ((toCommAssociatedModules X τ).obj F) :=
  sorry

/-- The internal Hom of two commutative associated modules, computed in the
universe-lifted module category as `InternalHom.obj`. -/
def associatedInternalHomLift {X : GroupoidsOver S} {τ : StandardTopology}
    (F G : commAssociatedModules X τ) : commAssociatedModulesLift X τ :=
  SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
    (commAssociatedStructureSheafLift X τ)
    ((commAssociatedModulesLiftFunctor X τ).obj F)
    ((commAssociatedModulesLiftFunctor X τ).obj G)

/-- `associatedInternalHomLift` is the canonical lifted internal Hom. -/
theorem associatedInternalHomLift_eq {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    associatedInternalHomLift F G =
      SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
        (commAssociatedStructureSheafLift X τ)
        ((commAssociatedModulesLiftFunctor X τ).obj F)
        ((commAssociatedModulesLiftFunctor X τ).obj G) :=
  rfl

/-- `associatedInternalHomLift` agrees with `(ihom _).obj _` on the lifted
commutative associated module category. -/
theorem associatedInternalHomLift_ihom {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    associatedInternalHomLift F G =
      (ihom ((commAssociatedModulesLiftFunctor X τ).obj F)).obj
        ((commAssociatedModulesLiftFunctor X τ).obj G) :=
  rfl

/-- Identity-on-Γ recovers an fppf module from its commutative fppf presentation. -/
def fromToCommAssociatedModulesIso {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u} (fppfRingedSite X)) :
    (fromCommAssociatedModules X).obj
        ((GroupoidsOver.toCommAssociatedModules X .fppf).obj M) ≅ M where
  hom :=
    { val :=
        (PresheafOfModules.Restriction.compComponentIso'
            (fromCommAssociatedCoefficient X .fppf)
            (toCommAssociatedCoefficient X .fppf)
            (𝟙 (structureSheaf X).obj)
            (fromCommAssociatedCoefficient_comp_toCommAssociatedCoefficient X .fppf)
            M.val).hom ≫
          (PresheafOfModules.Restriction.idComponentIso'
            (𝟙 (structureSheaf X).obj) rfl M.val).inv }
  inv :=
    { val :=
        (PresheafOfModules.Restriction.idComponentIso'
            (𝟙 (structureSheaf X).obj) rfl M.val).hom ≫
          (PresheafOfModules.Restriction.compComponentIso'
            (fromCommAssociatedCoefficient X .fppf)
            (toCommAssociatedCoefficient X .fppf)
            (𝟙 (structureSheaf X).obj)
            (fromCommAssociatedCoefficient_comp_toCommAssociatedCoefficient X .fppf)
            M.val).inv }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Pointwise tensor of universe lifts as a bilinear map into the lift of the
module-category tensor. -/
noncomputable def moduleTensorLiftBilinear {X : GroupoidsOver S}
    {τ : StandardTopology} (M N : commAssociatedModules X τ) :
    SectionBilinearMap.{u + 1, u} (commAssociatedStructureSheafLift X τ)
      ((commAssociatedModulesLiftFunctor X τ).obj M)
      ((commAssociatedModulesLiftFunctor X τ).obj N)
      ((commAssociatedModulesLiftFunctor X τ).obj
        (moduleTensorAssociated M N)) where
  app U :=
    LinearMap.mk₂ ((commAssociatedStructureSheafLift X τ).obj.obj U)
      (fun x y ↦
        ULift.up
          (((associatedModuleTensorIso M N).hom.val.app U).hom
            ((moduleSheafificationUnitToVal.{u + 1, u, u, u}
                (commAssociatedStructureSheaf X τ)
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app U
              (x.down ⊗ₜ y.down))))
      sorry sorry sorry sorry
  naturality := sorry

/-- Canonical comparison from the tensor product of universe lifts to the universe
lift of the module-category tensor. -/
noncomputable def moduleTensorLiftComparison {X : GroupoidsOver S}
    {τ : StandardTopology} (M N : commAssociatedModules X τ) :
    moduleTensorAssociatedLift
      ((commAssociatedModulesLiftFunctor X τ).obj M)
      ((commAssociatedModulesLiftFunctor X τ).obj N) ⟶
    (commAssociatedModulesLiftFunctor X τ).obj (moduleTensorAssociated M N) :=
  SectionBilinearMap.hom.{u + 1, u} (moduleTensorLiftBilinear M N)

/-- `moduleTensorLiftComparison` is the bilinear pairing of universe lifts of
pure tensors. -/
theorem moduleTensorLiftComparison_eq {X : GroupoidsOver S}
    {τ : StandardTopology} (M N : commAssociatedModules X τ) :
    moduleTensorLiftComparison M N =
      SectionBilinearMap.hom.{u + 1, u} (moduleTensorLiftBilinear M N) :=
  sorry

/-- Target (and, via currying, source) functoriality of the lifted internal Hom. -/
def associatedInternalHomLiftCongr {X : GroupoidsOver S} {τ : StandardTopology}
    {F₁ F₂ G₁ G₂ : commAssociatedModules X τ} (f : F₂ ⟶ F₁) (g : G₁ ⟶ G₂) :
    associatedInternalHomLift F₁ G₁ ⟶ associatedInternalHomLift F₂ G₂ :=
  let O := commAssociatedStructureSheafLift X τ
  let L := commAssociatedModulesLiftFunctor X τ
  (SheafOfModules.RingedSite.InternalHom.homEquiv O (L.obj F₂)
        (associatedInternalHomLift F₁ G₁) (L.obj G₂))
    (tensorHom (L.map f) (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
      (SheafOfModules.RingedSite.InternalHom.homEquiv O (L.obj F₁)
            (associatedInternalHomLift F₁ G₁) (L.obj G₁)).symm
        (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
      L.map g)

/-- `associatedInternalHomLiftCongr` is the currying of `tensorHom` against
evaluation, followed by the lifted target map. -/
theorem associatedInternalHomLiftCongr_eq {X : GroupoidsOver S}
    {τ : StandardTopology} {F₁ F₂ G₁ G₂ : commAssociatedModules X τ}
    (f : F₂ ⟶ F₁) (g : G₁ ⟶ G₂) :
    associatedInternalHomLiftCongr f g =
      (SheafOfModules.RingedSite.InternalHom.homEquiv
          (commAssociatedStructureSheafLift X τ)
          ((commAssociatedModulesLiftFunctor X τ).obj F₂)
          (associatedInternalHomLift F₁ G₁)
          ((commAssociatedModulesLiftFunctor X τ).obj G₂))
        (tensorHom ((commAssociatedModulesLiftFunctor X τ).map f)
            (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
          (SheafOfModules.RingedSite.InternalHom.homEquiv
                (commAssociatedStructureSheafLift X τ)
                ((commAssociatedModulesLiftFunctor X τ).obj F₁)
                (associatedInternalHomLift F₁ G₁)
                ((commAssociatedModulesLiftFunctor X τ).obj G₁)).symm
            (𝟙 (associatedInternalHomLift F₁ G₁)) ≫
          (commAssociatedModulesLiftFunctor X τ).map g) :=
  sorry

/-- The comparison determined by an evaluation `F ⊗ H ⟶ G`: transport to `τ`,
lift universes, and curry into the actual sheaf of local morphisms. -/
def internalHomComparison {X : GroupoidsOver S} (τ : StandardTopology)
    (F G H : QCoh X) (ev : quasicoherentTensor F H ⟶ G) :
    (commAssociatedModulesLiftFunctor X τ).obj
      ((toCommAssociatedModules X τ).obj H) ⟶
    associatedInternalHomLift
      ((toCommAssociatedModules X τ).obj F)
      ((toCommAssociatedModules X τ).obj G) :=
  SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
      (commAssociatedStructureSheafLift X τ)
      ((commAssociatedModulesLiftFunctor X τ).obj
        ((toCommAssociatedModules X τ).obj F))
      ((commAssociatedModulesLiftFunctor X τ).obj
        ((toCommAssociatedModules X τ).obj H))
      ((commAssociatedModulesLiftFunctor X τ).obj
        ((toCommAssociatedModules X τ).obj G))
    (moduleTensorLiftComparison
        ((toCommAssociatedModules X τ).obj F)
        ((toCommAssociatedModules X τ).obj H) ≫
      (commAssociatedModulesLiftFunctor X τ).map
        (tensorComparison τ F H ≫ (toCommAssociatedModules X τ).map ev))

/-- `internalHomComparison` is the currying of the lifted tensor comparison
followed by evaluation. -/
theorem internalHomComparison_eq {X : GroupoidsOver S} (τ : StandardTopology)
    (F G H : QCoh X) (ev : quasicoherentTensor F H ⟶ G) :
    internalHomComparison τ F G H ev =
      SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
          (commAssociatedStructureSheafLift X τ)
          ((commAssociatedModulesLiftFunctor X τ).obj
            ((toCommAssociatedModules X τ).obj F))
          ((commAssociatedModulesLiftFunctor X τ).obj
            ((toCommAssociatedModules X τ).obj H))
          ((commAssociatedModulesLiftFunctor X τ).obj
            ((toCommAssociatedModules X τ).obj G))
        (moduleTensorLiftComparison
            ((toCommAssociatedModules X τ).obj F)
            ((toCommAssociatedModules X τ).obj H) ≫
          (commAssociatedModulesLiftFunctor X τ).map
            (tensorComparison τ F H ≫ (toCommAssociatedModules X τ).map ev)) :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
