/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorScalarExtension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.ConcreteHom

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.FMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionComparison

/-!
# Pullback of modules on algebraic spaces

A morphism of algebraic spaces induces a morphism of small étale ringed topoi. The associated
module inverse image preserves quasi-coherence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Type direct image uses restriction to small charts, genuine right Kan extension,
and evaluation on the geometric fiber product. -/
def typePushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology Y) (Type u) :=
  AlgebraicGeometry.AlgebraicSpace.EtaleTopos.directImage f

/-- The constructed inverse-image functor and its actual adjunction witness right adjointness. -/
instance typePushforward_isRightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (typePushforward f).IsRightAdjoint :=
  (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.adjunction f).isRightAdjoint

/-- The constructed geometric inverse image is left exact. -/
instance typePushforward_leftAdjoint_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : PreservesFiniteLimits (typePushforward f).leftAdjoint := sorry

/-- The canonical morphism of topoi stores the genuine inverse image, unit and counit. -/
def morphismOfTopoi {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) :=
  AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos.topos f

/-- The canonical internal-ring lift of the genuine direct-image functor. -/
def ringPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) RingCat.{u} ⥤ Sheaf (smallEtaleTopology Y) RingCat.{u} :=
  AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos.ringPushforward f

/-- Forgetting ring structure gives the specified type-valued direct image. -/
def ringPushforwardForgetIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ringPushforward f ⋙ sheafCompose (smallEtaleTopology Y) (forget RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget RingCat.{u}) ⋙ typePushforward f :=
  AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos.forgetIso f

/-- The component of `f^♯` on an étale square is pullback of global sections along the
underlying scheme morphism. -/
def structureFMap_app {X Y : AlgebraicSpace S} {f : X ⟶ Y} (sq : EtaleSquare f) :
    (structureSheaf Y).obj.obj (op sq.right) ⟶
      (structureSheaf X).obj.obj (op sq.left) :=
  (forget₂ CommRingCat RingCat).map sq.map.left.appTop

/-- The étale square associated to a map from a scheme étale over `X` into `X ×_Y V`. -/
def etaleSquareOfArrow {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleToSpaces X).op) :
    EtaleSquare f where
  left := a.right.unop
  right := V
  map :=
    (yonedaEquiv (a.hom.unop.left ≫ etaleBaseChangeSnd f V) : a.right.unop.left ⟶ V.left)
  w := sorry

/-- The cone of `f^♯` components presenting the map `𝒪_Y(V) ⟶ 𝒪_X(X ×_Y V)`. -/
def structureSheafMapCone {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
        (smallEtaleToSpaces X).op ⋙ (structureSheaf X).obj) where
  pt := (structureSheaf Y).obj.obj (op V)
  π :=
    { app := fun a => structureFMap_app (etaleSquareOfArrow f V a)
      naturality := fun _ _ _ => sorry }

/-- The component at `V` of the direct-image structure-sheaf map `𝒪_Y ⟶ f_* 𝒪_X`. -/
def structureSheafMap_app {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : (smallEtaleSite Y)ᵒᵖ) :
    (structureSheaf Y).obj.obj V ⟶
      ((ringPushforward f).obj (structureSheaf X)).obj.obj V :=
  (AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos.structureMap f).hom.app V

/-- The direct-image form of `f^♯`, as a morphism of ring sheaves on `Y_étale`. -/
def structureSheafMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    structureSheaf Y ⟶ (ringPushforward f).obj (structureSheaf X) :=
  AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos.structureMap f

/-- The direct-image structure map is compatible with the canonical internal-ring operations. -/
theorem structureSheafMap_isRingCompatible {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    @RingedSite.ToposHom.Direct.IsRingCompatible (ringedSite X) (ringedSite Y) _ _
      (morphismOfTopoi f) (ringPushforward f) (ringPushforwardForgetIso f)
      (structureSheafMap f) :=
  sorry

/-- The morphism of small étale ringed topoi associated to a morphism of algebraic spaces. -/
def ringedToposHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    RingedSite.ToposHom (ringedSite X) (ringedSite Y) :=
  AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos.ringedHom f

/-- Inverse image preserves commutativity of the existing structure-ring multiplication. -/
theorem inverseStructureRing_mul_comm {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : (smallEtaleSite X)ᵒᵖ)
    (x y : ((ringedToposHom f).toTopos.ringInverseImage.obj (structureSheaf Y)).obj.obj U) :
    x * y = y * x := sorry

/-- The target structure-ring multiplication is the original multiplication of global sections. -/
theorem structureRing_mul_comm {X : AlgebraicSpace S} (U : (smallEtaleSite X)ᵒᵖ)
    (x y : (structureSheaf X).obj.obj U) : x * y = y * x :=
  @mul_comm Γ(U.unop.left.left, ⊤) _ x y

/-- The scalar adjunction comes from actual sectionwise tensors and local scheme sheafification. -/
def structureMapScalarAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    -- Local instance justification (defeq pin): the tensor functor must use the explicit chartwise sheafification adjunction also selected in the body.
    letI : HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
      (AlgebraicGeometry.AlgebraicSpace.SmallEtale.Sheafification.adjunction (X := X) AddCommGrpCat.{u}).isRightAdjoint
    SheafOfModules.TensorScalarExtension.functor (ringedToposHom f).structureMap
      (inverseStructureRing_mul_comm f) (structureRing_mul_comm (X := X)) ⊣
        SheafOfModules.restrictScalars (ringedToposHom f).structureMap :=
  -- Local instance justification (defeq pin): match the chartwise sheafification witness in the result type so its actual tensor unit and counit are retained.
  letI : HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u} :=
    (AlgebraicGeometry.AlgebraicSpace.SmallEtale.Sheafification.adjunction (X := X) AddCommGrpCat.{u}).isRightAdjoint
  SheafOfModules.TensorScalarExtension.adjunction (ringedToposHom f).structureMap
    (inverseStructureRing_mul_comm f) (structureRing_mul_comm (X := X))

/-- Restriction of scalars is right adjoint to the specified tensor/sheafification functor. -/
instance restrictScalars_structureMap_isRightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (SheafOfModules.restrictScalars.{u} (ringedToposHom f).structureMap).IsRightAdjoint :=
  (structureMapScalarAdjunction f).isRightAdjoint

namespace Modules

/-- The pullback functor `f* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of sheaves of modules on the small étale
ringed sites of algebraic spaces. -/
def pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Y.Modules ⥤ X.Modules :=
  (ringedToposHom f).modulePullback

/-- The pullback of modules along a morphism of algebraic spaces is the module pullback of the
associated morphism of ringed topoi. -/
theorem pullback_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pullback f = (ringedToposHom f).modulePullback :=
  rfl

/-- Comparison with the abstract ringed-topos pullback. The scalar adjoint is already
the specified tensor/sheafification adjoint, so this presentation uses identity maps. -/
def pullbackIsoTopos {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    pullback f ≅ (ringedToposHom f).modulePullback :=
  Iso.refl _

/-- Quasi-coherence as an object property is preserved by module pullback. -/
theorem pullback_quasiCoherentModuleProperty {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {F : Y.Modules} (hF : quasiCoherentModuleProperty Y F) :
    quasiCoherentModuleProperty X ((pullback f).obj F) :=
  sorry

/-- Pullback along a morphism of algebraic spaces preserves quasi-coherent module sheaves. -/
@[stacks 03GA]
instance pullback_isQuasicoherent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent] :
    ((pullback f).obj F).IsQuasicoherent :=
  pullback_quasiCoherentModuleProperty f (inferInstance : F.IsQuasicoherent)

end Modules

namespace QCoh

/-- Pullback of quasi-coherent modules along a morphism of algebraic spaces. -/
def pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) : QCoh Y ⥤ QCoh X :=
  ObjectProperty.FullSubcategory.restrict (Modules.pullback f) sorry

/-- The underlying module sheaf of a pulled-back quasi-coherent module is the usual module
pullback. -/
theorem pullback_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : QCoh Y) :
    ((pullback f).obj F).obj = (Modules.pullback f).obj F.obj :=
  sorry

end QCoh

end AlgebraicGeometry.AlgebraicSpace
