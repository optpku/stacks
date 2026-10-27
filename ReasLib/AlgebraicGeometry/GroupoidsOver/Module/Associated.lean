/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.TopologyComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic

/-!
# Associated module presentations and topology transport
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

/-- Ring-to-abelian-group sheaf composition exists on an associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_ring_addCommGrp
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Commutative-ring-to-ring sheaf composition exists on an associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_commRing
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Commutative-ring-to-ring sheaf composition exists in universe `u + 1` on an
associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_commRing_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on an associated `τ`-topology. -/
instance associatedTopology_hasWeakSheafify
    (X : GroupoidsOver S) (τ : StandardTopology) :
    HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u} :=
  sorry

/-- On an associated `τ`-topology, sheafification equivalences are the locally
bijective morphisms. -/
instance associatedTopology_wEqualsLocallyBijective
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists in universe `u + 1` on an
associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_addCommGrp_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists in universe `u + 1` on an
associated `τ`-topology. -/
instance associatedTopology_hasWeakSheafify_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  sorry

/-- On an associated `τ`-topology, sheafification equivalences in universe `u + 1`
are the locally bijective morphisms. -/
instance associatedTopology_wEqualsLocallyBijective_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- Weak sheafification exists on double slices of an associated `τ`-topology. -/
instance associatedTopology_over_over_hasWeakSheafify (X : GroupoidsOver S)
    (τ : StandardTopology) :
    ∀ U, ∀ V : Over U,
      HasWeakSheafify (((X.associatedTopology τ).over U).over V)
        AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on double slices of an associated `τ`-topology
are the locally bijective morphisms. -/
instance associatedTopology_over_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) (τ : StandardTopology) :
    ∀ U, ∀ V : Over U,
      (((X.associatedTopology τ).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  sorry

/-- The category of sheaves of modules on `(X_τ, 𝒪_X)`. -/
abbrev associatedModules (X : GroupoidsOver S) (τ : StandardTopology) :=
  SheafOfModules.{u} (associatedStructureSheaf X τ)

/-- The associated module category is the category of modules over the associated
structure sheaf. -/
theorem associatedModules_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    associatedModules X τ =
      SheafOfModules.{u} (associatedStructureSheaf X τ) :=
  sorry

/-- The associated module category has colimits of every universe-compatible
shape. -/
instance associatedModules_hasColimitsOfShape (X : GroupoidsOver S)
    (τ : StandardTopology) (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (associatedModules X τ) :=
  sorry

/-- The fppf module category of `X` has colimits of every universe-compatible
shape. -/
instance fppfModules_hasColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (RingedSite.ModuleCat.{u} (ringedSite X)) :=
  sorry

/-- The commutative global-sections presheaf on the big `τ`-site of `S` is a
sheaf. -/
theorem bigCommStructurePresheaf_isSheaf (τ : StandardTopology) :
    Presheaf.IsSheaf (τ.overTopology S) ((Over.forget S).op ⋙ Scheme.Γ) :=
  sorry

/-- The commutative structure sheaf on the big `τ`-site of `S`. -/
def bigCommStructureSheaf (τ : StandardTopology) :
    Sheaf (τ.overTopology S) CommRingCat.{u} :=
  ⟨(Over.forget S).op ⋙ Scheme.Γ, bigCommStructurePresheaf_isSheaf τ⟩

/-- The commutative structure sheaf `𝒪_X` on the associated `τ`-site, obtained as
the inverse image `p⁻¹ 𝒪` of the big `τ`-commutative structure sheaf. -/
def commAssociatedStructureSheaf (X : GroupoidsOver S) (τ : StandardTopology) :
    Sheaf (X.associatedTopology τ) CommRingCat.{u} :=
  (X.p.sheafPushforwardContinuous CommRingCat.{u}
      (X.associatedTopology τ) (τ.overTopology S)).obj
    (bigCommStructureSheaf τ)

/-- `commAssociatedStructureSheaf` is the continuous pushforward of the big `τ`
commutative structure sheaf along the projection of `X`. -/
theorem commAssociatedStructureSheaf_def (X : GroupoidsOver S)
    (τ : StandardTopology) :
    commAssociatedStructureSheaf X τ =
      (X.p.sheafPushforwardContinuous CommRingCat.{u}
          (X.associatedTopology τ) (τ.overTopology S)).obj
        (bigCommStructureSheaf τ) :=
  sorry

/-- The associated `τ`-site of `X`, with commutative structure sheaf `𝒪_X`. -/
abbrev commAssociatedRingedSite (X : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofCommRingSheaf (X.associatedTopology τ)
    (commAssociatedStructureSheaf X τ)

/-- The structure sheaf of `commAssociatedRingedSite X τ` is the ring sheaf
underlying the commutative associated structure sheaf. -/
theorem commAssociatedRingedSite_structureSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (commAssociatedRingedSite X τ).structureSheaf =
      CategoryTheory.Sheaf.ringSheafOfComm (commAssociatedStructureSheaf X τ) :=
  sorry

/-- The category of sheaves of modules on the commutative associated `τ`-ringed
site of `X`. -/
abbrev commAssociatedModules (X : GroupoidsOver S) (τ : StandardTopology) :=
  RingedSite.ModuleCat.{u} (commAssociatedRingedSite X τ)

/-- `commAssociatedModules` is the module category of
`commAssociatedRingedSite`. -/
theorem commAssociatedModules_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    commAssociatedModules X τ =
      RingedSite.ModuleCat.{u} (commAssociatedRingedSite X τ) :=
  sorry

/-- The commutative associated module category has colimits of every
universe-compatible shape. -/
instance commAssociatedModules_hasColimitsOfShape (X : GroupoidsOver S)
    (τ : StandardTopology) (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (commAssociatedModules X τ) :=
  sorry

/-- Tensor product of modules on the commutative associated `τ`-site. -/
noncomputable abbrev moduleTensorAssociated {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    commAssociatedModules X τ :=
  SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} F G

/-- `moduleTensorAssociated` is the ringed-site tensor product. -/
theorem moduleTensorAssociated_eq {X : GroupoidsOver S} {τ : StandardTopology}
    (F G : commAssociatedModules X τ) :
    moduleTensorAssociated F G =
      SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} F G :=
  sorry

/-- The universe lift of the commutative associated `τ`-structure presheaf. -/
abbrev commAssociatedStructurePresheafLift (X : GroupoidsOver S)
    (τ : StandardTopology) :
    X.totalᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (commAssociatedStructureSheaf X τ).obj ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted commutative associated structure presheaf is a sheaf. -/
theorem commAssociatedStructurePresheafLift_isSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    Presheaf.IsSheaf (X.associatedTopology τ)
      (commAssociatedStructurePresheafLift X τ) :=
  sorry

/-- The universe-lifted commutative structure sheaf on the associated `τ`-site. -/
def commAssociatedStructureSheafLift (X : GroupoidsOver S)
    (τ : StandardTopology) :
    Sheaf (X.associatedTopology τ) CommRingCat.{u + 1} :=
  ⟨commAssociatedStructurePresheafLift X τ,
    commAssociatedStructurePresheafLift_isSheaf X τ⟩

/-- The associated `τ`-site equipped with the universe-lifted commutative
structure sheaf. -/
abbrev commAssociatedRingedSiteLift (X : GroupoidsOver S)
    (τ : StandardTopology) : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommSheafMax (X.associatedTopology τ)
    (commAssociatedStructureSheafLift X τ)

/-- The structure sheaf of `commAssociatedRingedSiteLift X τ` is the underlying
ring sheaf of the lifted commutative structure sheaf. -/
theorem commAssociatedRingedSiteLift_structureSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (commAssociatedRingedSiteLift X τ).structureSheaf =
      CategoryTheory.Sheaf.ringSheafOfComm
        (commAssociatedStructureSheafLift X τ) :=
  sorry

/-- The category of universe-lifted modules on the commutative associated
`τ`-site of `X`. -/
abbrev commAssociatedModulesLift (X : GroupoidsOver S) (τ : StandardTopology) :=
  RingedSite.ModuleCat.{u + 1} (commAssociatedRingedSiteLift X τ)

/-- Tensor product of universe-lifted modules on the commutative associated
`τ`-site. -/
noncomputable abbrev moduleTensorAssociatedLift {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModulesLift X τ) :
    commAssociatedModulesLift X τ :=
  SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u + 1} F G

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
    RingedSite.ModuleCat.{u} (ringedSite X) ⥤ associatedModules X τ where
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
    (F : RingedSite.ModuleCat.{u} (ringedSite X)) :
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
    RingedSite.ModuleCat.{u} (ringedSite X) ⥤
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
    (F : RingedSite.ModuleCat.{u} (ringedSite X)) :
    ((toCommAssociatedModules X τ).obj F).val =
      (PresheafOfModules.restrictScalars
        (toCommAssociatedCoefficient X τ)).obj F.val :=
  sorry

/-- Identity-on-Γ transport of the commutative fppf presentation back to fppf modules. -/
def fromCommAssociatedModules (X : GroupoidsOver S) :
    commAssociatedModules X .fppf ⥤
      RingedSite.ModuleCat.{u} (ringedSite X) where
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
    RingedSite.ModuleCat.{u} (ringedSite X) ⥤ etaleModules X where
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
    (F : RingedSite.ModuleCat.{u} (ringedSite X)) :
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

/-- Identity-on-Γ identifies associated `τ`-modules with the restriction of the
commutative fppf presentation. -/
def toCommAssociatedModules_restrictIso {X : GroupoidsOver S}
    (τ : StandardTopology) (F : QCoh X) :
    (toCommAssociatedModules X τ).obj F ≅
      (restrictCommAssociatedModules X τ .fppf rfl).obj
        ((toCommAssociatedModules X .fppf).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
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
  (SheafOfModules.fullyFaithfulForget _).preimageIso
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

/-- Identity-on-Γ recovers an fppf module from its commutative fppf presentation. -/
def fromToCommAssociatedModulesIso {X : GroupoidsOver S}
    (M : RingedSite.ModuleCat.{u} (ringedSite X)) :
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

end QCoh

end AlgebraicGeometry.GroupoidsOver
