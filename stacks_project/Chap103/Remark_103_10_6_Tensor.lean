module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import stacks_project.Chap96.Lemma_96_15_1_Tensor
public import stacks_project.Chap103.Lemma_103_10_1
public import stacks_project.Chap103.Proposition_103_8_1_FppfSheaf
public import stacks_project.Chap103.Remark_103_10_6_SiteSheafification

/-!
# Tensorators for QCoh → LQCoh^{fbc} → Mod and for Q

Étale tensor of `LQCoh^{fbc}` objects is packaged without redeclaring
`LQCohFbc.tensor` from Proposition 103.8.1, which cannot be imported with
`toQCoh`. The inclusion tensorators and the adjunct `Q`-tensorator live here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open AlgebraicGeometry.GroupoidsOver
open PresheafOfModules
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Package the étale tensor of two `LQCoh^{fbc}` objects as an object of
`LQCoh^{fbc}`. This is the same data as `LQCohFbc.tensor` in
Proposition 103.8.1, restated on the `toQCoh` import path. -/
def LQCohFbc.ofModuleTensorEtale {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : LQCohFbc X) : LQCohFbc X :=
  ⟨moduleTensorEtale F.obj G.obj, sorry⟩

/-- The underlying étale module of `LQCohFbc.ofModuleTensorEtale F G` is the
étale tensor product. -/
theorem LQCohFbc.ofModuleTensorEtale_obj {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : LQCohFbc X) :
    (LQCohFbc.ofModuleTensorEtale F G).obj = moduleTensorEtale F.obj G.obj :=
  rfl

/-- The tensor product of two morphisms of `LQCoh^{fbc}` modules, computed as
the étale module tensor map of the underlying morphisms. -/
def LQCohFbc.tensorHom {X : GroupoidsOver S} [AlgebraicStack X]
    {F₁ F₂ G₁ G₂ : LQCohFbc X} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    LQCohFbc.ofModuleTensorEtale F₁ G₁ ⟶ LQCohFbc.ofModuleTensorEtale F₂ G₂ :=
  ObjectProperty.homMk (moduleTensorMap.{u + 1, u, u} f.hom g.hom)

/-- The underlying étale morphism of `LQCohFbc.tensorHom f g` is the module
tensor map. -/
theorem LQCohFbc.tensorHom_hom {X : GroupoidsOver S} [AlgebraicStack X]
    {F₁ F₂ G₁ G₂ : LQCohFbc X} (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    (LQCohFbc.tensorHom f g).hom =
      moduleTensorMap.{u + 1, u, u} f.hom g.hom :=
  rfl

/-- Identity-on-Γ comparison of the commutative étale structure presheaf with
the commutative fppf structure presheaf. -/
def commEtaleToFppfPresheaf (X : GroupoidsOver S) :
    (commEtaleStructureSheaf X).obj ⟶ (commFppfStructureSheaf X).obj where
  app := fun _ ↦ 𝟙 _
  naturality := fun _ _ _ ↦ sorry

/-- Restriction of scalars of a commutative fppf module to the commutative
étale structure presheaf, along `commEtaleToFppfPresheaf`. -/
def restrictToCommEtaleVal (X : GroupoidsOver S) (M : commFppfModules X) :
    PresheafOfModules (ringPresheaf (commEtaleStructureSheaf X).obj) :=
  (restrictScalars (presheafStructureMap (commEtaleToFppfPresheaf X))).obj M.val

/-- Restriction of scalars of a commutative fppf module presheaf to the
commutative étale structure presheaf, along `commEtaleToFppfPresheaf`. -/
def restrictPresheafToCommEtale (X : GroupoidsOver S)
    (M : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj)) :
    PresheafOfModules (ringPresheaf (commEtaleStructureSheaf X).obj) :=
  (restrictScalars (presheafStructureMap (commEtaleToFppfPresheaf X))).obj M

/-- `restrictToCommEtaleVal` is restriction of scalars of the underlying
presheaf. -/
theorem restrictToCommEtaleVal_eq (X : GroupoidsOver S) (M : commFppfModules X) :
    restrictToCommEtaleVal X M = restrictPresheafToCommEtale X M.val :=
  rfl

/-- View a commutative fppf module as an étale module by identity-on-Γ
restriction of scalars to `commEtaleStructureSheaf`. -/
def etaleOfCommRestrict {X : GroupoidsOver S} (M : commFppfModules X) :
    etaleModules X where
  val := restrictToCommEtaleVal X M
  isSheaf := sorry

/-- The morphism of étale views induced by a morphism of commutative fppf
modules. -/
def etaleOfCommRestrictMap {X : GroupoidsOver S} {M N : commFppfModules X}
    (f : M ⟶ N) :
    etaleOfCommRestrict M ⟶ etaleOfCommRestrict N where
  val :=
    (restrictScalars (presheafStructureMap (commEtaleToFppfPresheaf X))).map f.val

/-- The underlying presheaf morphism of `etaleOfCommRestrictMap` is restriction
of scalars of `f.val`. -/
theorem etaleOfCommRestrictMap_val {X : GroupoidsOver S}
    {M N : commFppfModules X} (f : M ⟶ N) :
    (etaleOfCommRestrictMap f).val =
      (restrictScalars (presheafStructureMap (commEtaleToFppfPresheaf X))).map
        f.val :=
  rfl

/-- Identity-on-Γ comparison from the commutative-étale restriction of
`toComm F.obj` to the étale restriction of `F`. -/
def QCoh.etaleOfCommRestrict_to_restriction {X : GroupoidsOver S}
    [AlgebraicStack X] (F : QCoh X) :
    etaleOfCommRestrict ((toCommFppfModules X).obj F.obj) ⟶
      (restriction X).obj F.obj where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Identity-on-Γ comparison from the étale restriction of `F` to the
commutative-étale restriction of `toComm F.obj`. -/
def QCoh.restriction_to_etaleOfCommRestrict {X : GroupoidsOver S}
    [AlgebraicStack X] (F : QCoh X) :
    (restriction X).obj F.obj ⟶
      etaleOfCommRestrict ((toCommFppfModules X).obj F.obj) where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Identity-on-Γ comparison from the étale restriction of the transported
fppf tensor to the commutative-étale restriction of that tensor. -/
def QCoh.restriction_tensor_to_etaleOfCommRestrict {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    ((QCoh.toLQCohFbc X).obj (QCoh.tensor F G)).obj ⟶
      etaleOfCommRestrict (QCoh.moduleTensor F G) where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Identity-on-Γ comparison from the commutative-étale restriction of the
transported fppf tensor to the étale restriction of that tensor. -/
def QCoh.etaleOfCommRestrict_tensor_to_restriction {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    etaleOfCommRestrict (QCoh.moduleTensor F G) ⟶
      ((QCoh.toLQCohFbc X).obj (QCoh.tensor F G)).obj where
  val :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }

/-- Componentwise identity-restriction isomorphism for a commutative fppf
module presheaf. -/
def restrictPresheafToCommEtale_appIso {X : GroupoidsOver S}
    (M : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj))
    (U : X.totalᵒᵖ) :
    (restrictPresheafToCommEtale X M).obj U ≅ M.obj U :=
  (ModuleCat.restrictScalarsId'App
      ((presheafStructureMap (commEtaleToFppfPresheaf X)).app U).hom
      rfl (M.obj U)).symm

/-- Componentwise identity-restriction isomorphism for `restrictToCommEtaleVal`. -/
def restrictToCommEtaleVal_appIso {X : GroupoidsOver S} (M : commFppfModules X)
    (U : X.totalᵒᵖ) :
    (restrictToCommEtaleVal X M).obj U ≅ M.val.obj U :=
  restrictPresheafToCommEtale_appIso M.val U

/-- Pointwise tensor of commutative-étale restrictions compared with the
restricted pointwise tensor, at a section. -/
def QCoh.restrictToCommEtaleVal_tensorObj_appIso {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) (U : X.totalᵒᵖ) :
    (Monoidal.tensorObj
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).obj U ≅
      (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val).obj U :=
  tensorIso
    (restrictToCommEtaleVal_appIso ((toCommFppfModules X).obj F.obj) U)
    (restrictToCommEtaleVal_appIso ((toCommFppfModules X).obj G.obj) U)

/-- Lax restriction tensor comparison for the identity-on-Γ ring map, from the
pointwise tensor of commutative-étale restrictions to the restriction of the
pointwise fppf tensor. -/
def QCoh.restrictToCommEtaleVal_tensorComparison {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    Monoidal.tensorObj
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj)) ⟶
      restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val) :=
  PresheafOfModules.Restriction.tensorComparison
    (commEtaleToFppfPresheaf X)
    ((toCommFppfModules X).obj F.obj).val
    ((toCommFppfModules X).obj G.obj).val

/-- `restrictToCommEtaleVal_tensorComparison` is the canonical restriction
tensor comparison. -/
theorem QCoh.restrictToCommEtaleVal_tensorComparison_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    QCoh.restrictToCommEtaleVal_tensorComparison F G =
      PresheafOfModules.Restriction.tensorComparison
        (commEtaleToFppfPresheaf X)
        ((toCommFppfModules X).obj F.obj).val
        ((toCommFppfModules X).obj G.obj).val :=
  rfl

/-- Oplax comparison from the restricted pointwise fppf tensor to the pointwise
tensor of commutative-étale restrictions, assembled from identity-restriction
isomorphisms. The ring map is `𝟙` on sections. -/
def QCoh.restrictPresheafTensor_to_tensorObj {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val) ⟶
      Monoidal.tensorObj
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj)) where
  app U :=
    (restrictPresheafToCommEtale_appIso
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val) U).hom ≫
      (QCoh.restrictToCommEtaleVal_tensorObj_appIso F G U).inv
  naturality := sorry

/-- The section of `restrictPresheafTensor_to_tensorObj` is the reverse of
`restrictPresheafToCommEtale_appIso` and the pointwise tensor iso. -/
theorem QCoh.restrictPresheafTensor_to_tensorObj_app {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) (U : X.totalᵒᵖ) :
    (QCoh.restrictPresheafTensor_to_tensorObj F G).app U =
      (restrictPresheafToCommEtale_appIso
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val) U).hom ≫
        (QCoh.restrictToCommEtaleVal_tensorObj_appIso F G U).inv :=
  rfl

/-- Unit comparison from étale sheafification of the restricted pointwise tensor
to the étale view of the fppf sheafification. -/
def QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).obj
        (restrictPresheafToCommEtale X
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val)) ⟶
      etaleOfCommRestrict
        (commFppfModuleTensor
          ((toCommFppfModules X).obj F.obj)
          ((toCommFppfModules X).obj G.obj)) :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
    X.total _ X.etaleTopology _
      (AlgebraicGeometry.GroupoidsOver.Sheafification.Etale.stackHasWeakSheafify X) _
    (commEtaleStructureSheaf X)
      (restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val))
      (etaleOfCommRestrict
        (commFppfModuleTensor
          ((toCommFppfModules X).obj F.obj)
          ((toCommFppfModules X).obj G.obj)))).symm
    ((restrictScalars (presheafStructureMap (commEtaleToFppfPresheaf X))).map
      (moduleSheafificationUnitToVal.{u + 1, u, u, u} (commFppfStructureSheaf X)
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val)))

/-- `sheafifyRestrict_to_etaleOfCommRestrictSheafification` is the sheafification
adjunct of restriction of the fppf sheafification unit. -/
theorem QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification_eq
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification F G =
      (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
    X.total _ X.etaleTopology _
      (AlgebraicGeometry.GroupoidsOver.Sheafification.Etale.stackHasWeakSheafify X) _
    (commEtaleStructureSheaf X)
          (restrictPresheafToCommEtale X
            (Monoidal.tensorObj
              ((toCommFppfModules X).obj F.obj).val
              ((toCommFppfModules X).obj G.obj).val))
          (etaleOfCommRestrict
            (commFppfModuleTensor
              ((toCommFppfModules X).obj F.obj)
              ((toCommFppfModules X).obj G.obj)))).symm
        ((restrictScalars (presheafStructureMap (commEtaleToFppfPresheaf X))).map
          (moduleSheafificationUnitToVal.{u + 1, u, u, u} (commFppfStructureSheaf X)
            (Monoidal.tensorObj
              ((toCommFppfModules X).obj F.obj).val
              ((toCommFppfModules X).obj G.obj).val))) :=
  rfl

/-- Adjunct of the restricted pointwise tensor comparison into the étale sheaf
tensor. -/
def QCoh.sheafifyRestrict_to_tensorEtale {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).obj
        (restrictPresheafToCommEtale X
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val)) ⟶
      moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)) :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
    X.total _ X.etaleTopology _
      (AlgebraicGeometry.GroupoidsOver.Sheafification.Etale.stackHasWeakSheafify X) _
    (commEtaleStructureSheaf X)
      (restrictPresheafToCommEtale X
        (Monoidal.tensorObj
          ((toCommFppfModules X).obj F.obj).val
          ((toCommFppfModules X).obj G.obj).val))
      (moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)))).symm
    (QCoh.restrictPresheafTensor_to_tensorObj F G ≫
      moduleSheafificationUnitToVal.{u + 1, u, u, u} (commEtaleStructureSheaf X)
        (Monoidal.tensorObj
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))) ≫
      (Functor.Monoidal.μIso
          (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X))
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
          (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).inv.val ≫
      (moduleTensorMap.{u + 1, u, u}
        (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
            (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).hom
        (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
            (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).hom).val)

/-- `sheafifyRestrict_to_tensorEtale` is the sheafification adjunct of the
restricted pointwise comparison followed by `μIso.inv` and
`moduleSheafificationValIso.hom` on the two factors. -/
theorem QCoh.sheafifyRestrict_to_tensorEtale_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    QCoh.sheafifyRestrict_to_tensorEtale F G =
      (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
    X.total _ X.etaleTopology _
      (AlgebraicGeometry.GroupoidsOver.Sheafification.Etale.stackHasWeakSheafify X) _
    (commEtaleStructureSheaf X)
          (restrictPresheafToCommEtale X
            (Monoidal.tensorObj
              ((toCommFppfModules X).obj F.obj).val
              ((toCommFppfModules X).obj G.obj).val))
          (moduleTensorEtale
            (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
            (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)))).symm
        (QCoh.restrictPresheafTensor_to_tensorObj F G ≫
          moduleSheafificationUnitToVal.{u + 1, u, u, u} (commEtaleStructureSheaf X)
            (Monoidal.tensorObj
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))) ≫
          (Functor.Monoidal.μIso
              (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X))
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
              (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).inv.val ≫
          (moduleTensorMap.{u + 1, u, u}
            (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
                (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).hom
            (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
                (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).hom).val) :=
  rfl

/-- Lax sheaf-tensor comparison from the étale sheaf tensor of commutative-étale
restrictions to étale sheafification of the restricted pointwise tensor. -/
def QCoh.tensorEtale_to_sheafifyRestrict {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)) ⟶
      (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).obj
        (restrictPresheafToCommEtale X
          (Monoidal.tensorObj
            ((toCommFppfModules X).obj F.obj).val
            ((toCommFppfModules X).obj G.obj).val)) :=
  moduleTensorMap.{u + 1, u, u}
      (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
          (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).inv
      (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
          (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).inv ≫
    (Functor.Monoidal.μIso
        (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
        (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).hom ≫
    (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).map
      (QCoh.restrictToCommEtaleVal_tensorComparison F G)

/-- `tensorEtale_to_sheafifyRestrict` is `moduleTensorMap` of
`moduleSheafificationValIso.inv`, then `μIso.hom`, then sheafification of
`restrictToCommEtaleVal_tensorComparison`. -/
theorem QCoh.tensorEtale_to_sheafifyRestrict_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    QCoh.tensorEtale_to_sheafifyRestrict F G =
      moduleTensorMap.{u + 1, u, u}
          (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
              (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))).inv
          (moduleSheafificationValIso.{u + 1, u, u, u} (commEtaleStructureSheaf X)
              (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj))).inv ≫
        (Functor.Monoidal.μIso
            (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X))
            (restrictToCommEtaleVal X ((toCommFppfModules X).obj F.obj))
            (restrictToCommEtaleVal X ((toCommFppfModules X).obj G.obj))).hom ≫
        (moduleSheafification.{u + 1, u, u, u} (commEtaleStructureSheaf X)).map
          (QCoh.restrictToCommEtaleVal_tensorComparison F G) :=
  rfl

/-- Lax sheaf-tensor comparison
`etaleOfCommRestrict F ⊗ etaleOfCommRestrict G ⟶ etaleOfCommRestrict (F ⊗ G)`,
as the étale sheaf-tensor comparison into sheafification of the restricted
pointwise tensor, then the sheafification unit adjunct, then
`commFppfModuleTensorIso.hom`. -/
def QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    moduleTensorEtale
        (etaleOfCommRestrict ((toCommFppfModules X).obj F.obj))
        (etaleOfCommRestrict ((toCommFppfModules X).obj G.obj)) ⟶
      etaleOfCommRestrict (QCoh.moduleTensor F G) :=
  QCoh.tensorEtale_to_sheafifyRestrict F G ≫
    QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification F G ≫
    etaleOfCommRestrictMap
      (commFppfModuleTensorIso
        ((toCommFppfModules X).obj F.obj)
        ((toCommFppfModules X).obj G.obj)).hom

/-- `tensorEtale_to_etaleOfCommRestrict_moduleTensor` is
`tensorEtale_to_sheafifyRestrict`, then the unit adjunct, then
`commFppfModuleTensorIso.hom`. -/
theorem QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor_eq
    {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X) :
    QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor F G =
      QCoh.tensorEtale_to_sheafifyRestrict F G ≫
        QCoh.sheafifyRestrict_to_etaleOfCommRestrictSheafification F G ≫
        etaleOfCommRestrictMap
          (commFppfModuleTensorIso
            ((toCommFppfModules X).obj F.obj)
            ((toCommFppfModules X).obj G.obj)).hom :=
  rfl

/-- Underlying étale morphism of the lax tensorator
`i(F) ⊗ i(G) ⟶ i(F ⊗ G)`, as a forward composite of identity-on-Γ
comparisons with the sheaf-tensor comparison. -/
def QCoh.toLQCohFbc_tensorator_hom {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : QCoh X) :
    (LQCohFbc.ofModuleTensorEtale
        ((QCoh.toLQCohFbc X).obj F) ((QCoh.toLQCohFbc X).obj G)).obj ⟶
      ((QCoh.toLQCohFbc X).obj (QCoh.tensor F G)).obj :=
  moduleTensorMap.{u + 1, u, u}
      (QCoh.restriction_to_etaleOfCommRestrict F)
      (QCoh.restriction_to_etaleOfCommRestrict G) ≫
    QCoh.tensorEtale_to_etaleOfCommRestrict_moduleTensor F G ≫
    QCoh.etaleOfCommRestrict_tensor_to_restriction F G

/-- Lax tensorator `i(F) ⊗ i(G) ⟶ i(F ⊗ G)` of `QCoh.toLQCohFbc`. The
source is the étale tensor of the images. -/
def QCoh.toLQCohFbc_tensorator {X : GroupoidsOver S} [AlgebraicStack X]
    (F G : QCoh X) :
    LQCohFbc.ofModuleTensorEtale
        ((QCoh.toLQCohFbc X).obj F) ((QCoh.toLQCohFbc X).obj G) ⟶
      (QCoh.toLQCohFbc X).obj (QCoh.tensor F G) :=
  ObjectProperty.homMk (QCoh.toLQCohFbc_tensorator_hom F G)

/-- The underlying étale morphism of `toLQCohFbc_tensorator` is
`toLQCohFbc_tensorator_hom`. -/
theorem QCoh.toLQCohFbc_tensorator_hom_eq {X : GroupoidsOver S}
    [AlgebraicStack X] (F G : QCoh X) :
    (QCoh.toLQCohFbc_tensorator F G).hom =
      QCoh.toLQCohFbc_tensorator_hom F G :=
  rfl

namespace QCoh

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- This changes coefficients only; it does not choose new module elements. -/
def fppfCoefficientToEtale (X : GroupoidsOver S) :
    (commFppfStructureSheaf X).obj ⟶ (commEtaleStructureSheaf X).obj where
  app := fun _ => 𝟙 _
  naturality := by intros; rfl

/-- Regard an étale module presheaf as a module over the fppf structure
presheaf by the identity coefficient map; sections and restrictions are retained. -/
def fppfViewPresheaf (H : etaleModules X) :
    PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj) :=
  (restrictScalars (presheafStructureMap (fppfCoefficientToEtale X))).obj H.val

/-- Equip the unchanged underlying module presheaf with its given fppf sheaf
property. The certificate changes no section data. -/
def fppfView (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf) :
    commFppfModules X := ⟨fppfViewPresheaf H, hH⟩

/-- The identity section map from a presheaf to its successive étale and
fppf coefficient restrictions, using the explicit identity-restriction iso. -/
def reverseCoefficientUnit
    (P : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj)) :
    P ⟶ (restrictScalars (presheafStructureMap (fppfCoefficientToEtale X))).obj
      (restrictPresheafToCommEtale X P) where
  app U := (ModuleCat.restrictScalarsId'App
    (((presheafStructureMap (commEtaleToFppfPresheaf X)).app U).hom.comp
      ((presheafStructureMap (fppfCoefficientToEtale X)).app U).hom) rfl (P.obj U)).inv
  naturality := by intros; rfl

/-- Extend the given presheaf map uniquely across fppf sheafification into
an already fppf-sheaf target, after the two identity coefficient changes. -/
def fromFppfSheafification (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    (moduleSheafification.{u + 1, u, u, u} (commFppfStructureSheaf X)).obj P ⟶ fppfView H hH :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
    X.total _ (inheritedFppfTopology X) _
      (AlgebraicGeometry.GroupoidsOver.Sheafification.stackHasWeakSheafify X) _
    (commFppfStructureSheaf X) P (fppfView H hH)).symm
    (reverseCoefficientUnit P ≫
      (restrictScalars (presheafStructureMap (fppfCoefficientToEtale X))).map g)

/-- The constructed descent map is characterised by its original presheaf
map under the actual sheafification adjunction. -/
theorem fromFppfSheafification_homEquiv (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    (moduleSheafificationHomEquiv.{u + 1, u, u, u}
      (commFppfStructureSheaf X) P (fppfView H hH))
        (fromFppfSheafification H hH P g) =
      reverseCoefficientUnit P ≫
        (restrictScalars (presheafStructureMap (fppfCoefficientToEtale X))).map g :=
  Equiv.apply_symm_apply _ _

/-- The extension agrees with the specified presheaf map on sections coming
from the sheafification unit. Both coefficient changes are identity on sections. -/
theorem fromFppfSheafification_unit (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    moduleSheafificationUnitToVal (commFppfStructureSheaf X) P ≫
        (fromFppfSheafification H hH P g).val =
      reverseCoefficientUnit P ≫
        (restrictScalars (presheafStructureMap (fppfCoefficientToEtale X))).map g := by
  calc
    _ = (moduleSheafificationHomEquiv.{u + 1, u, u, u}
        (commFppfStructureSheaf X) P (fppfView H hH))
          (fromFppfSheafification H hH P g) := by
      ext U x
      rfl
    _ = _ := fromFppfSheafification_homEquiv H hH P g

/-- The same modules after the two identity coefficient changes have the
identity section map. No inverse selected by an IsIso proof is used. -/
def etaleOfFppfViewToOriginal (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf) :
    etaleOfCommRestrict (fppfView H hH) ⟶ H where
  val := { app := fun _ => 𝟙 _, naturality := by intros; rfl }

/-- Explicit reverse descent to a target which is already an fppf sheaf. -/
def descendToEtale (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    etaleOfCommRestrict ((moduleSheafification.{u + 1, u, u, u}
      (commFppfStructureSheaf X)).obj P) ⟶ H :=
  etaleOfCommRestrictMap (fromFppfSheafification H hH P g) ≫
    etaleOfFppfViewToOriginal H hH

/-- Étale descent is the restricted fppf sheafification extension followed
by the identity comparison back to the original étale target. -/
theorem descendToEtale_eq (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    descendToEtale H hH P g =
      etaleOfCommRestrictMap (fromFppfSheafification H hH P g) ≫
        etaleOfFppfViewToOriginal H hH := rfl

/-- The descended étale morphism has the prescribed value on every section
from the original presheaf. In particular, taking the pointwise tensor as `P`
fixes its values on pure tensors before sheafification. -/
theorem descendToEtale_unit (H : etaleModules X)
    (hH : Presheaf.IsSheaf (inheritedFppfTopology X) (fppfViewPresheaf H).presheaf)
    (P : PresheafOfModules (ringPresheaf (commFppfStructureSheaf X).obj))
    (g : restrictPresheafToCommEtale X P ⟶ H.val) :
    (restrictScalars (presheafStructureMap (commEtaleToFppfPresheaf X))).map
        (moduleSheafificationUnitToVal (commFppfStructureSheaf X) P) ≫
        (descendToEtale H hH P g).val = g := by
  ext U x
  exact congrArg (fun k => k.app U x) (fromFppfSheafification_unit H hH P g)

/-- The actual étale tensor of the two included quasi-coherent modules is
an fppf sheaf by Proposition 103.8.1 (1), not by a new witness assumption. -/
theorem targetTensor_isFppfSheaf (F G : QCoh X) :
    Presheaf.IsSheaf (inheritedFppfTopology X)
      (fppfViewPresheaf (LQCohFbc.ofModuleTensorEtale
        ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj).presheaf := by
  exact @isSheaf_fppf_of_lqcohFbc _ _ _
    ((LQCohFbc.ofModuleTensorEtale ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj)
    (LQCohFbc.ofModuleTensorEtale ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).property.1
    (LQCohFbc.ofModuleTensorEtale ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).property.2

/-- A presheaf map from pure tensors into the actual target étale tensor. -/
def pointwiseToEtaleTensor (F G : QCoh X) :
    restrictPresheafToCommEtale X
      (Monoidal.tensorObj ((toCommFppfModules X).obj F.obj).val
        ((toCommFppfModules X).obj G.obj).val) ⟶
      (LQCohFbc.ofModuleTensorEtale ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj.val :=
  (@moduleSheafificationHomEquiv.{u + 1, u, u, u}
    X.total _ X.etaleTopology _
      (AlgebraicGeometry.GroupoidsOver.Sheafification.Etale.stackHasWeakSheafify X) _
    (commEtaleStructureSheaf X) _ _)
      (sheafifyRestrict_to_tensorEtale F G) ≫
    (moduleTensorMap.{u + 1, u, u}
      (etaleOfCommRestrict_to_restriction F) (etaleOfCommRestrict_to_restriction G)).val

/-- Forward descent of the fppf tensor to the actual étale tensor. -/
def toLQCohFbc_tensoratorOplaxHom (F G : QCoh X) :
    ((toLQCohFbc X).obj (tensor F G)).obj ⟶
      (LQCohFbc.ofModuleTensorEtale ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G)).obj :=
  restriction_tensor_to_etaleOfCommRestrict F G ≫
    etaleOfCommRestrictMap
      (commFppfModuleTensorIso ((toCommFppfModules X).obj F.obj)
        ((toCommFppfModules X).obj G.obj)).inv ≫
    descendToEtale _ (targetTensor_isFppfSheaf F G) _ (pointwiseToEtaleTensor F G)

/-- The reverse tensor comparison in `LQCohFbc`, whose underlying map descends
the pointwise tensor map from fppf sheafification to the étale tensor. -/
def toLQCohFbc_tensoratorOplax (F G : QCoh X) :
    (toLQCohFbc X).obj (tensor F G) ⟶
      LQCohFbc.ofModuleTensorEtale ((toLQCohFbc X).obj F) ((toLQCohFbc X).obj G) :=
  CategoryTheory.ObjectProperty.homMk (toLQCohFbc_tensoratorOplaxHom F G)

end QCoh

/-- The north-west arrow of the tensor triangle: the tensor of adjunction
counits `ε_F ⊗ ε_G`. -/
def LQCohFbc.tensorCounit {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.ofModuleTensorEtale
        ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj F))
        ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj G)) ⟶
      LQCohFbc.ofModuleTensorEtale F G :=
  LQCohFbc.tensorHom (adj.counit.app F) (adj.counit.app G)

/-- `tensorCounit` is the tensor of the two counit components. -/
theorem LQCohFbc.tensorCounit_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.tensorCounit adj F G =
      LQCohFbc.tensorHom (adj.counit.app F) (adj.counit.app G) :=
  rfl

/-- The source composite `i(QF ⊗ QG) ⟶ i(QF) ⊗ i(QG) ⟶ F ⊗ G`, obtained by
descending the explicit presheaf map to the fppf-sheaf target, then applying
`ε_F ⊗ ε_G`. -/
def LQCohFbc.toQCoh_μ_pre {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    (QCoh.toLQCohFbc X).obj
        (QCoh.tensor ((LQCohFbc.toQCoh X).obj F) ((LQCohFbc.toQCoh X).obj G)) ⟶
      LQCohFbc.ofModuleTensorEtale F G :=
  QCoh.toLQCohFbc_tensoratorOplax ((LQCohFbc.toQCoh X).obj F)
      ((LQCohFbc.toQCoh X).obj G) ≫
    LQCohFbc.tensorCounit adj F G

/-- `toQCoh_μ_pre` is the explicit oplax tensorator, then `ε_F ⊗ ε_G`. -/
theorem LQCohFbc.toQCoh_μ_pre_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.toQCoh_μ_pre adj F G =
      QCoh.toLQCohFbc_tensoratorOplax ((LQCohFbc.toQCoh X).obj F)
          ((LQCohFbc.toQCoh X).obj G) ≫
        LQCohFbc.tensorCounit adj F G :=
  rfl

/-- The tensorator `μ : Q(F) ⊗ Q(G) ⟶ Q(F ⊗ G)` of `Q = LQCohFbc.toQCoh`, as
the adjunct of `ε_F ⊗ ε_G`. The lax i-tensorator identifies the source of
that counit tensor with the inclusion of the quasi-coherent tensor. -/
def LQCohFbc.toQCoh_μ {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    QCoh.tensor ((LQCohFbc.toQCoh X).obj F) ((LQCohFbc.toQCoh X).obj G) ⟶
      (LQCohFbc.toQCoh X).obj (LQCohFbc.ofModuleTensorEtale F G) :=
  (adj.homEquiv _ _) (LQCohFbc.toQCoh_μ_pre adj F G)

/-- `toQCoh_μ` is the adjunct of `toQCoh_μ_pre`. -/
theorem LQCohFbc.toQCoh_μ_eq {X : GroupoidsOver S} [AlgebraicStack X]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F G : LQCohFbc X) :
    LQCohFbc.toQCoh_μ adj F G =
      (adj.homEquiv _ _) (LQCohFbc.toQCoh_μ_pre adj F G) :=
  rfl

/-- Restriction of a quasi-coherent morphism to the small étale site of an
object of `X`, as `toLQCohFbc` followed by étale inclusion and small-étale
restriction. This matches Lemma 103.4.2 while avoiding the
`projection_isContinuous` diamond. -/
def QCoh.restrictToSmallEtaleViaRestriction (X : GroupoidsOver S)
    [AlgebraicStack X] (x : X.total) :
    QCoh X ⥤
      RingedSite.ModuleCat.{u}
        (Scheme.Etale.Small.ringedSite (X.p.obj x).left) :=
  QCoh.toLQCohFbc X ⋙ LQCohFbc.inclusion X ⋙ restrictModulesToSmallEtale X x

/-- `restrictToSmallEtaleViaRestriction` is `toLQCohFbc`, then étale inclusion,
then small-étale restriction. -/
theorem QCoh.restrictToSmallEtaleViaRestriction_eq (X : GroupoidsOver S)
    [AlgebraicStack X] (x : X.total) :
    QCoh.restrictToSmallEtaleViaRestriction X x =
      QCoh.toLQCohFbc X ⋙ LQCohFbc.inclusion X ⋙
        restrictModulesToSmallEtale X x :=
  rfl

end AlgebraicGeometry.GroupoidsOver
