module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_11_2_Pullback

/-!
# Tensor and internal Hom of quasi-coherent modules on an algebraic stack

The tensor product of quasi-coherent `𝒪_𝒳`-modules is the transport of the
commutative fppf module tensor back to `QCoh(𝒪_𝒳)`. Internal Hom from a finite
locally free quasi-coherent module is identified by an evaluation whose
currying is invertible on the universe-lifted commutative fppf site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
  AlgebraicGeometry.GroupoidsOver CategoryTheory.MonoidalCategory
  SheafOfModules SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Commutative-ring-to-ring sheaf composition exists on the inherited fppf
topology of a category fibred in groupoids. -/
instance inheritedFppfTopology_hasSheafCompose_commRing (X : GroupoidsOver S) :
    (inheritedFppfTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Commutative-ring-to-ring sheaf composition exists in universe `u + 1` on the
inherited fppf topology. -/
instance inheritedFppfTopology_hasSheafCompose_commRing_succ
    (X : GroupoidsOver S) :
    (inheritedFppfTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- The commutative structure sheaf on the big fppf site of `S` is a sheaf. -/
theorem bigFppfCommStructurePresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      ((Over.forget S).op ⋙ Scheme.Γ) :=
  sorry

/-- The commutative structure sheaf on the big fppf site of `S`. -/
def bigFppfCommStructureSheaf (S : Scheme.{u}) :
    Sheaf (Scheme.fppfTopology.over S) CommRingCat.{u} :=
  ⟨(Over.forget S).op ⋙ Scheme.Γ, bigFppfCommStructurePresheaf_isSheaf S⟩

/-- The commutative structure sheaf `𝒪_𝒳` on the inherited fppf site. -/
def commFppfStructureSheaf (X : GroupoidsOver S) :
    Sheaf (inheritedFppfTopology X) CommRingCat.{u} :=
  (X.p.sheafPushforwardContinuous CommRingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).obj
    (bigFppfCommStructureSheaf S)

/-- `commFppfStructureSheaf` is the continuous pushforward of the big fppf
commutative structure sheaf. -/
theorem commFppfStructureSheaf_eq (X : GroupoidsOver S) :
    commFppfStructureSheaf X =
      (X.p.sheafPushforwardContinuous CommRingCat.{u}
          (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).obj
        (bigFppfCommStructureSheaf S) :=
  sorry

/-- The commutative fppf ringed site of `𝒳`. -/
abbrev commFppfRingedSite (X : GroupoidsOver S) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofCommRingSheaf (inheritedFppfTopology X) (commFppfStructureSheaf X)

/-- The category of modules on the commutative fppf ringed site of `𝒳`. -/
abbrev commFppfModules (X : GroupoidsOver S) :=
  RingedSite.ModuleCat.{u} (commFppfRingedSite X)

/-- Weak sheafification of abelian groups exists on the inherited fppf topology. -/
instance inheritedFppfTopology_hasWeakSheafify (X : GroupoidsOver S) :
    HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on the inherited fppf topology are the locally
bijective morphisms. -/
instance inheritedFppfTopology_wEqualsLocallyBijective (X : GroupoidsOver S) :
    (inheritedFppfTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Weak sheafification of abelian groups exists in universe `u + 1` on the
inherited fppf topology. -/
instance inheritedFppfTopology_hasWeakSheafify_succ (X : GroupoidsOver S) :
    HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{u + 1} :=
  sorry

/-- Sheafification equivalences in universe `u + 1` on the inherited fppf
topology are the locally bijective morphisms. -/
instance inheritedFppfTopology_wEqualsLocallyBijective_succ
    (X : GroupoidsOver S) :
    (inheritedFppfTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- Weak sheafification exists on every slice of the inherited fppf topology. -/
instance inheritedFppfTopology_over_hasWeakSheafify (X : GroupoidsOver S) :
    ∀ U, HasWeakSheafify ((inheritedFppfTopology X).over U) AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the inherited fppf topology are the
locally bijective morphisms. -/
instance inheritedFppfTopology_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) :
    ∀ U, ((inheritedFppfTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- Weak sheafification exists on slices in universe `u + 1`. -/
instance inheritedFppfTopology_over_hasWeakSheafify_succ
    (X : GroupoidsOver S) :
    ∀ U, HasWeakSheafify ((inheritedFppfTopology X).over U)
      AddCommGrpCat.{u + 1} :=
  sorry

/-- Sheafification equivalences on slices in universe `u + 1` are the locally
bijective morphisms. -/
instance inheritedFppfTopology_over_wEqualsLocallyBijective_succ
    (X : GroupoidsOver S) :
    ∀ U, ((inheritedFppfTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  sorry

/-- Identity-on-Γ comparison of the fppf structure presheaf with the underlying
ring presheaf of the commutative fppf structure sheaf. -/
def fppfToCommStructurePresheafIso (X : GroupoidsOver S) :
    (structureSheaf X).obj ≅
      (commFppfStructureSheaf X).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u} :=
  (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S) ≪≫
    isoWhiskerLeft X.p.op
      (CategoryTheory.Functor.associator (Over.forget S).op Scheme.Γ
        (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    (CategoryTheory.Functor.associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
      (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
    (isoWhiskerRight
      ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
          (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
        (bigFppfCommStructureSheaf S))
      (forget₂ CommRingCat.{u} RingCat.{u})).symm

/-- `fppfToCommStructurePresheafIso` is the composite of the continuous
pushforward identifications with the associator for `Γ ⋙ forget₂`. -/
theorem fppfToCommStructurePresheafIso_eq (X : GroupoidsOver S) :
    fppfToCommStructurePresheafIso X =
      (X.p.sheafPushforwardContinuousCompSheafToPresheafIso RingCat.{u}
          (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S) ≪≫
        isoWhiskerLeft X.p.op
          (CategoryTheory.Functor.associator (Over.forget S).op Scheme.Γ
            (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
        (CategoryTheory.Functor.associator X.p.op ((Over.forget S).op ⋙ Scheme.Γ)
          (forget₂ CommRingCat.{u} RingCat.{u})).symm ≪≫
        (isoWhiskerRight
          ((X.p.sheafPushforwardContinuousCompSheafToPresheafIso CommRingCat.{u}
              (inheritedFppfTopology X) (Scheme.fppfTopology.over S)).app
            (bigFppfCommStructureSheaf S))
          (forget₂ CommRingCat.{u} RingCat.{u})).symm :=
  sorry

/-- Coefficient morphism from the commutative fppf structure sheaf to the
ring-valued fppf structure sheaf. -/
def toCommFppfCoefficient (X : GroupoidsOver S) :
    ((commFppfStructureSheaf X).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      (structureSheaf X).obj :=
  (fppfToCommStructurePresheafIso X).inv

/-- `toCommFppfCoefficient` is the inverse of `fppfToCommStructurePresheafIso`. -/
theorem toCommFppfCoefficient_eq (X : GroupoidsOver S) :
    toCommFppfCoefficient X = (fppfToCommStructurePresheafIso X).inv :=
  sorry

/-- Coefficient morphism from the ring-valued fppf structure sheaf to the
commutative fppf structure sheaf. -/
def fromCommFppfCoefficient (X : GroupoidsOver S) :
    (structureSheaf X).obj ⟶
      ((commFppfStructureSheaf X).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}) :=
  (fppfToCommStructurePresheafIso X).hom

/-- `fromCommFppfCoefficient` is the forward map of
`fppfToCommStructurePresheafIso`. -/
theorem fromCommFppfCoefficient_eq (X : GroupoidsOver S) :
    fromCommFppfCoefficient X = (fppfToCommStructurePresheafIso X).hom :=
  sorry

/-- The two coefficient morphisms compose to the identity of the fppf structure
presheaf. -/
theorem fromCommFppfCoefficient_comp_toCommFppfCoefficient
    (X : GroupoidsOver S) :
    fromCommFppfCoefficient X ≫ toCommFppfCoefficient X =
      𝟙 (structureSheaf X).obj :=
  sorry

/-- The two coefficient morphisms compose to the identity of the commutative
fppf structure presheaf. -/
theorem toCommFppfCoefficient_comp_fromCommFppfCoefficient
    (X : GroupoidsOver S) :
    toCommFppfCoefficient X ≫ fromCommFppfCoefficient X =
      𝟙 ((commFppfStructureSheaf X).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Transport of fppf `𝒪_𝒳`-modules to the commutative fppf presentation. -/
def toCommFppfModules (X : GroupoidsOver S) :
    RingedSite.ModuleCat.{u} (fppfRingedSite X) ⥤ commFppfModules X where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars (toCommFppfCoefficient X)).obj F.val
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars (toCommFppfCoefficient X)).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `toCommFppfModules` is restriction of scalars along
`toCommFppfCoefficient`. -/
theorem toCommFppfModules_obj (X : GroupoidsOver S)
    (F : RingedSite.ModuleCat.{u} (fppfRingedSite X)) :
    ((toCommFppfModules X).obj F).val =
      (PresheafOfModules.restrictScalars (toCommFppfCoefficient X)).obj F.val :=
  sorry

/-- Identity-on-Γ transport of the commutative fppf presentation back to fppf
modules. -/
def fromCommFppfModules (X : GroupoidsOver S) :
    commFppfModules X ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X) where
  obj F :=
    { val :=
        (PresheafOfModules.restrictScalars (fromCommFppfCoefficient X)).obj F.val
      isSheaf := sorry }
  map f :=
    { val :=
        (PresheafOfModules.restrictScalars (fromCommFppfCoefficient X)).map f.val }
  map_id := sorry
  map_comp := sorry

/-- The object action of `fromCommFppfModules` is restriction of scalars along
`fromCommFppfCoefficient`. -/
theorem fromCommFppfModules_obj (X : GroupoidsOver S) (F : commFppfModules X) :
    ((fromCommFppfModules X).obj F).val =
      (PresheafOfModules.restrictScalars (fromCommFppfCoefficient X)).obj F.val :=
  sorry

/-- Wrap a module-presheaf isomorphism as an isomorphism of commutative fppf
module sheaves. -/
def sheafIsoOfValIso {X : GroupoidsOver S} {M N : commFppfModules X}
    (e : M.val ≅ N.val) : M ≅ N where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identity-on-Γ restriction of scalars recovers a commutative fppf module. -/
def toFromCommFppfModulesIso {X : GroupoidsOver S} (M : commFppfModules X) :
    (toCommFppfModules X).obj ((fromCommFppfModules X).obj M) ≅ M :=
  sheafIsoOfValIso
    (PresheafOfModules.Restriction.compComponentIso'
        (toCommFppfCoefficient X) (fromCommFppfCoefficient X)
        (𝟙 ((commFppfStructureSheaf X).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u}))
        (toCommFppfCoefficient_comp_fromCommFppfCoefficient X) M.val ≪≫
      (PresheafOfModules.Restriction.idComponentIso'
        (𝟙 ((commFppfStructureSheaf X).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u})) rfl M.val).symm)

/-- The universe lift of the commutative fppf structure presheaf. -/
abbrev commFppfStructurePresheafLift (X : GroupoidsOver S) :
    X.totalᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (commFppfStructureSheaf X).obj ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted commutative fppf structure presheaf is a sheaf. -/
theorem commFppfStructurePresheafLift_isSheaf (X : GroupoidsOver S) :
    Presheaf.IsSheaf (inheritedFppfTopology X)
      (commFppfStructurePresheafLift X) :=
  sorry

/-- The universe-lifted commutative structure sheaf on the inherited fppf site. -/
def commFppfStructureSheafLift (X : GroupoidsOver S) :
    Sheaf (inheritedFppfTopology X) CommRingCat.{u + 1} :=
  ⟨commFppfStructurePresheafLift X, commFppfStructurePresheafLift_isSheaf X⟩

/-- The inherited fppf site equipped with the universe-lifted commutative
structure sheaf. -/
abbrev commFppfRingedSiteLift (X : GroupoidsOver S) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommSheafMax (inheritedFppfTopology X)
    (commFppfStructureSheafLift X)

/-- The category of universe-lifted modules on the commutative fppf site. -/
abbrev commFppfModulesLift (X : GroupoidsOver S) :=
  RingedSite.ModuleCat.{u + 1} (commFppfRingedSiteLift X)

/-- The universe lift of one value of a commutative fppf module. -/
noncomputable abbrev commFppfModuleLiftObj {X : GroupoidsOver S}
    (M : commFppfModules X) (U : X.totalᵒᵖ) :
    ModuleCat.{u + 1} ((commFppfStructureSheafLift X).obj.obj U) :=
  (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
    ((ModuleCat.uliftFunctor.{u + 1, u}
      ((CategoryTheory.Sheaf.ringSheafOfComm
        (commFppfStructureSheaf X)).obj.obj U)).obj (M.val.obj U))

/-- The universe-lifted action of a module morphism preserves addition. -/
theorem commFppfModuleLiftMap_add {X : GroupoidsOver S}
    {M N : commFppfModules X} (f : M ⟶ N) (U : X.totalᵒᵖ)
    (x y : commFppfModuleLiftObj M U) :
    ULift.up (f.val.app U (x + y).down) =
      ULift.up (f.val.app U x.down) + ULift.up (f.val.app U y.down) :=
  sorry

/-- The universe-lifted action of a module morphism preserves scalar
multiplication. -/
theorem commFppfModuleLiftMap_smul {X : GroupoidsOver S}
    {M N : commFppfModules X} (f : M ⟶ N) (U : X.totalᵒᵖ)
    (r : (commFppfStructureSheafLift X).obj.obj U)
    (x : commFppfModuleLiftObj M U) :
    (ULift.up (f.val.app U (r • x).down) : commFppfModuleLiftObj N U) =
      @SMul.smul ((commFppfStructureSheafLift X).obj.obj U)
        (commFppfModuleLiftObj N U)
        (ModuleCat.isModule (commFppfModuleLiftObj N U)).toSMul r
        (ULift.up (f.val.app U x.down)) :=
  sorry

/-- The universe lift of a component of a morphism of commutative fppf modules. -/
noncomputable def commFppfModuleLiftMap {X : GroupoidsOver S}
    {M N : commFppfModules X} (f : M ⟶ N) (U : X.totalᵒᵖ) :
    commFppfModuleLiftObj M U ⟶ commFppfModuleLiftObj N U :=
  let source : ModuleCat.{u + 1}
      ((commFppfStructureSheafLift X).obj.obj U) :=
    commFppfModuleLiftObj M U
  let target : ModuleCat.{u + 1}
      ((commFppfStructureSheafLift X).obj.obj U) :=
    commFppfModuleLiftObj N U
  @ModuleCat.ofHom ((commFppfStructureSheafLift X).obj.obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (f.val.app U x.down)
      map_add' := commFppfModuleLiftMap_add f U
      map_smul' := commFppfModuleLiftMap_smul f U }

/-- The scalar-restricted target of a lifted restriction map. -/
noncomputable abbrev commFppfModuleLiftRestrictionTarget
    {X : GroupoidsOver S} (M : commFppfModules X) {U V : X.totalᵒᵖ}
    (i : U ⟶ V) :=
  (ModuleCat.restrictScalars
    ((commFppfStructureSheafLift X).obj.map i).hom).obj
    (commFppfModuleLiftObj M V)

/-- A lifted restriction map preserves addition. -/
theorem commFppfModuleLiftRestrictionMap_add {X : GroupoidsOver S}
    (M : commFppfModules X) {U V : X.totalᵒᵖ} (i : U ⟶ V)
    (x y : commFppfModuleLiftObj M U) :
    (ULift.up (M.val.map i (x + y).down) :
        commFppfModuleLiftRestrictionTarget M i) =
      ULift.up (M.val.map i x.down) + ULift.up (M.val.map i y.down) :=
  sorry

/-- A lifted restriction map preserves scalar multiplication. -/
theorem commFppfModuleLiftRestrictionMap_smul {X : GroupoidsOver S}
    (M : commFppfModules X) {U V : X.totalᵒᵖ} (i : U ⟶ V)
    (r : (commFppfStructureSheafLift X).obj.obj U)
    (x : commFppfModuleLiftObj M U) :
    (ULift.up (M.val.map i (r • x).down) :
        commFppfModuleLiftRestrictionTarget M i) =
      @SMul.smul ((commFppfStructureSheafLift X).obj.obj U)
        (commFppfModuleLiftRestrictionTarget M i)
        (ModuleCat.isModule
          (commFppfModuleLiftRestrictionTarget M i)).toSMul r
        (ULift.up (M.val.map i x.down)) :=
  sorry

/-- The universe lift of a restriction map of a commutative fppf module. -/
noncomputable def commFppfModuleLiftRestrictionMap {X : GroupoidsOver S}
    (M : commFppfModules X) {U V : X.totalᵒᵖ} (i : U ⟶ V) :
    commFppfModuleLiftObj M U ⟶ commFppfModuleLiftRestrictionTarget M i :=
  let source : ModuleCat.{u + 1}
      ((commFppfStructureSheafLift X).obj.obj U) :=
    commFppfModuleLiftObj M U
  let target : ModuleCat.{u + 1}
      ((commFppfStructureSheafLift X).obj.obj U) :=
    commFppfModuleLiftRestrictionTarget M i
  @ModuleCat.ofHom ((commFppfStructureSheafLift X).obj.obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (M.val.map i x.down)
      map_add' := commFppfModuleLiftRestrictionMap_add M i
      map_smul' := commFppfModuleLiftRestrictionMap_smul M i }

/-- The universe lift of the underlying presheaf of a commutative fppf module. -/
noncomputable def commFppfModuleLiftPresheaf {X : GroupoidsOver S}
    (M : commFppfModules X) :
    PresheafOfModules.{u + 1}
      (CategoryTheory.Sheaf.ringSheafOfComm
        (commFppfStructureSheafLift X)).obj where
  obj U := commFppfModuleLiftObj M U
  map i := commFppfModuleLiftRestrictionMap M i
  map_id := sorry
  map_comp := sorry

/-- Universe lifting preserves the sheaf condition on the inherited fppf site. -/
theorem commFppfModuleLiftPresheaf_isSheaf {X : GroupoidsOver S}
    (M : commFppfModules X) :
    Presheaf.IsSheaf (inheritedFppfTopology X)
      (commFppfModuleLiftPresheaf M).presheaf :=
  sorry

/-- The universe lift of a morphism of commutative fppf modules. -/
noncomputable def commFppfModuleLiftNatTrans {X : GroupoidsOver S}
    {M N : commFppfModules X} (f : M ⟶ N) :
    commFppfModuleLiftPresheaf M ⟶ commFppfModuleLiftPresheaf N where
  app U := commFppfModuleLiftMap f U
  naturality := sorry

/-- The functorial universe lift from commutative fppf modules to their
universe-`u + 1` presentation. -/
noncomputable def commFppfModulesLiftFunctor (X : GroupoidsOver S) :
    commFppfModules X ⥤ commFppfModulesLift X where
  obj M :=
    ⟨commFppfModuleLiftPresheaf M, commFppfModuleLiftPresheaf_isSheaf M⟩
  map f := ⟨commFppfModuleLiftNatTrans f⟩
  map_id := sorry
  map_comp := sorry

/-- Tensor product of commutative fppf modules, computed as the sheafification of
the pointwise tensor. -/
def commFppfModuleTensor {X : GroupoidsOver S} (F G : commFppfModules X) :
    commFppfModules X :=
  (moduleSheafification.{u + 1, u, u, u} (commFppfStructureSheaf X)).obj
    (PresheafOfModules.Monoidal.tensorObj F.val G.val)

/-- The sheafified pointwise tensor is canonically isomorphic to the monoidal
tensor product in the commutative fppf module category. -/
noncomputable def commFppfModuleTensorIso {X : GroupoidsOver S}
    (F G : commFppfModules X) :
    commFppfModuleTensor F G ≅
      SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} F G :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commFppfStructureSheaf X))
      F.val G.val).symm ≪≫
    tensorIso
      (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
        (commFppfStructureSheaf X) F)
      (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
        (commFppfStructureSheaf X) G)

end AlgebraicGeometry.GroupoidsOver

@[expose] public section

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Tensor product of two quasi-coherent modules, computed in the commutative
fppf presentation of `Mod(𝒪_𝒳)`. -/
abbrev moduleTensor [AlgebraicStack X] (F G : QCoh X) : commFppfModules X :=
  SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u}
    ((toCommFppfModules X).obj F.obj) ((toCommFppfModules X).obj G.obj)

/-- `moduleTensor` is the ringed-site tensor product of the transported modules. -/
theorem moduleTensor_eq [AlgebraicStack X] (F G : QCoh X) :
    moduleTensor F G =
      SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u}
        ((toCommFppfModules X).obj F.obj) ((toCommFppfModules X).obj G.obj) :=
  sorry

/-- The tensor product of two quasi-coherent `𝒪_𝒳`-modules, computed in
`Mod(𝒪_𝒳)`, as an object of `QCoh(𝒪_𝒳)`. The underlying fppf module is the
transport of the commutative module tensor. -/
def tensor [AlgebraicStack X] (F G : QCoh X) : QCoh X where
  obj := (fromCommFppfModules X).obj (moduleTensor F G)
  property := sorry

/-- The underlying fppf module of `tensor` is the transport of the commutative
fppf module tensor. -/
theorem tensor_obj [AlgebraicStack X] (F G : QCoh X) :
    (tensor F G).obj = (fromCommFppfModules X).obj (moduleTensor F G) :=
  sorry

/-- Canonical comparison in the commutative fppf presentation from the module
tensor to the identity-on-Γ transport of `tensor F G`. -/
def tensorComparison [AlgebraicStack X] (F G : QCoh X) :
    moduleTensor F G ⟶ (toCommFppfModules X).obj (tensor F G).obj :=
  (toFromCommFppfModulesIso (moduleTensor F G)).inv

/-- `tensorComparison` is the inverse of `toFromCommFppfModulesIso`. -/
theorem tensorComparison_eq [AlgebraicStack X] (F G : QCoh X) :
    tensorComparison F G = (toFromCommFppfModulesIso (moduleTensor F G)).inv :=
  sorry

/-- Tensor products computed in `Mod(𝒪_𝒳)` agree with the quasi-coherent tensor. -/
instance tensorComparison_isIso [AlgebraicStack X] (F G : QCoh X) :
    IsIso (tensorComparison F G) :=
  (toFromCommFppfModulesIso (moduleTensor F G)).isIso_inv

/-- Pointwise tensor of universe lifts as a bilinear map into the lift of the
module-category tensor. -/
noncomputable def moduleTensorLiftBilinear [AlgebraicStack X]
    (M N : commFppfModules X) :
    SheafOfModules.RingedSite.SectionBilinearMap.{u + 1, u}
      (commFppfStructureSheafLift X)
      ((commFppfModulesLiftFunctor X).obj M)
      ((commFppfModulesLiftFunctor X).obj N)
      ((commFppfModulesLiftFunctor X).obj
        (SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} M N)) where
  app U :=
    LinearMap.mk₂ ((commFppfStructureSheafLift X).obj.obj U)
      (fun x y ↦
        ULift.up
          (((commFppfModuleTensorIso M N).hom.val.app U).hom
            ((moduleSheafificationUnitToVal.{u + 1, u, u, u}
                (commFppfStructureSheaf X)
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app U
              (x.down ⊗ₜ y.down))))
      sorry sorry sorry sorry
  naturality := sorry

/-- Comparison from the tensor of universe lifts to the lift of the module
tensor. -/
noncomputable def moduleTensorLiftComparison [AlgebraicStack X]
    (M N : commFppfModules X) :
    SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u + 1}
      ((commFppfModulesLiftFunctor X).obj M)
      ((commFppfModulesLiftFunctor X).obj N) ⟶
    (commFppfModulesLiftFunctor X).obj
      (SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} M N) :=
  SheafOfModules.RingedSite.SectionBilinearMap.hom.{u + 1, u}
    (moduleTensorLiftBilinear M N)

/-- The comparison determined by an evaluation `F ⊗ H ⟶ G`: transport to the
commutative fppf presentation, lift universes, and curry into the actual sheaf
of local morphisms. -/
def internalHomComparison [AlgebraicStack X] (F G H : QCoh X)
    (ev : tensor F H ⟶ G) :
    (commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj H.obj) ⟶
      SheafOfModules.RingedSite.InternalHom.obj.{u + 1, u, u + 1}
        (commFppfStructureSheafLift X)
        ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj F.obj))
        ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj G.obj)) :=
  SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
      (commFppfStructureSheafLift X)
      ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj F.obj))
      ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj H.obj))
      ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj G.obj))
    (moduleTensorLiftComparison
        ((toCommFppfModules X).obj F.obj)
        ((toCommFppfModules X).obj H.obj) ≫
      (commFppfModulesLiftFunctor X).map
        (tensorComparison F H ≫ (toCommFppfModules X).map ev.hom))

/-- `internalHomComparison` is the currying of the lifted tensor comparison
followed by evaluation. -/
theorem internalHomComparison_eq [AlgebraicStack X] (F G H : QCoh X)
    (ev : tensor F H ⟶ G) :
    internalHomComparison F G H ev =
      SheafOfModules.RingedSite.InternalHom.homEquiv.{u + 1, u}
          (commFppfStructureSheafLift X)
          ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj F.obj))
          ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj H.obj))
          ((commFppfModulesLiftFunctor X).obj ((toCommFppfModules X).obj G.obj))
        (moduleTensorLiftComparison
            ((toCommFppfModules X).obj F.obj)
            ((toCommFppfModules X).obj H.obj) ≫
          (commFppfModulesLiftFunctor X).map
            (tensorComparison F H ≫ (toCommFppfModules X).map ev.hom)) :=
  rfl

/-- If `F` is finite locally free, there is a quasi-coherent internal Hom from
`F` to `G` in `Mod(𝒪_𝒳)`, witnessed by an evaluation whose currying is an
isomorphism on the universe-lifted commutative fppf site. -/
theorem internalHom [AlgebraicStack X] (F G : QCoh X)
    [SheafOfModules.IsFiniteLocallyFree F.obj] :
    ∃ (H : QCoh X) (ev : tensor F H ⟶ G),
      IsIso (internalHomComparison F G H ev) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh

