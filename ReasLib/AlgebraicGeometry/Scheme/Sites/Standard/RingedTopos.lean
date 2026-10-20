/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose

@[expose] public section
open AlgebraicGeometry CategoryTheory Functor Opposite
open scoped MorphismOfTopoiIn
noncomputable section
universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- Ring-valued sheaves on a standard big `τ`-site compose with `forget RingCat`. -/
instance overTopology_hasSheafCompose_ring (τ : StandardTopology) (S : Scheme.{u}) :
    (τ.overTopology S).HasSheafCompose (forget RingCat.{u}) :=
  sorry

section RingedToposHom

variable (τ : StandardTopology) {T S : Scheme.{u}} (f : T ⟶ S)
variable [HasSheafify (τ.overTopology T) (Type u)]
variable [∀ P : (Over T)ᵒᵖ ⥤ Type u, (Over.map f).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over T)ᵒᵖ ⥤ RingCat.{u}, (Over.map f).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (Over.map f).op]

/-- Inverse-image comparison `(Over.map f)⁻¹ 𝒪_S ⟶ 𝒪_T` on global sections, induced by
`Over.mapForget f`. -/
def ringedToposHom_inverseImageStructureMap :
    ((Over.map f).sheafPushforwardContinuous RingCat.{u}
        (τ.overTopology T) (τ.overTopology S)).obj
      (ringedSite τ S).structureSheaf ⟶
      (ringedSite τ T).structureSheaf :=
  ⟨Scheme.Site.inverseStructurePresheafMap
    (Over.forget T) (Over.forget S) (Over.map f) (Over.mapForget f).inv⟩

/-- Direct-image form of the structure-sheaf map of `ringedToposHom`. -/
def ringedToposHom_structureMap :
    (ringedSite τ S).structureSheaf ⟶
      ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
        (τ.overTopology T) (τ.overTopology S)).obj
        (ringedSite τ T).structureSheaf :=
  ((Over.map f).sheafAdjunctionCocontinuous RingCat.{u}
      (τ.overTopology T) (τ.overTopology S)).homEquiv _ _
    (ringedToposHom_inverseImageStructureMap τ f)

/-- The morphism of topoi underlying `ringedToposHom τ f`. -/
def ringedToposHom_toToposVal :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (τ.overTopology S) (τ.overTopology T) :=
  (Over.map f).morphismOfTopoiInOfCocontinuous
    (τ.overTopology T) (τ.overTopology S)

/-- Forgetting rings commutes with the cocontinuous direct image along `Over.map f`. -/
def ringedToposHom_forgetIso :
    ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
          (τ.overTopology T) (τ.overTopology S)) ⋙
        sheafCompose (τ.overTopology S) (forget RingCat.{u}) ≅
      sheafCompose (τ.overTopology T) (forget RingCat.{u}) ⋙
        (ringedToposHom_toToposVal τ f).pushforward :=
  CategoryTheory.Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (Over.map f) (forget RingCat.{u}) (τ.overTopology T) (τ.overTopology S)

/-- The direct-image structure map of `ringedToposHom` preserves internal-ring operations. -/
theorem ringedToposHom_isRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (ringedSite τ T) (ringedSite τ S) _ _
      (ringedToposHom_toToposVal τ f)
      ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
        (τ.overTopology T) (τ.overTopology S))
      (ringedToposHom_forgetIso τ f)
      (ringedToposHom_structureMap τ f) :=
  sorry

/-- The morphism of big `τ`-ringed topoi induced by a morphism of schemes, presented by
the cocontinuous functor `Over.map f`. The continuous site-level presentation of the same
geometric morphism is `pullbackRingedHom τ f`. -/
def ringedToposHom :
    RingedSite.ToposHom (ringedSite τ T) (ringedSite τ S) :=
  @RingedSite.ToposHom.ofDirectImage (ringedSite τ T) (ringedSite τ S) _ _
    (ringedToposHom_toToposVal τ f)
    ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
      (τ.overTopology T) (τ.overTopology S))
    (ringedToposHom_forgetIso τ f)
    (ringedToposHom_structureMap τ f)
    (ringedToposHom_isRingCompatible τ f)

/-- The underlying morphism of topoi of `ringedToposHom τ f` is the cocontinuous
morphism of topoi induced by `Over.map f`. -/
theorem ringedToposHom_toTopos :
    (ringedToposHom τ f).toTopos = ringedToposHom_toToposVal τ f :=
  rfl

/-- The inverse-image structure map of `ringedToposHom τ f` is the mate of
`ringedToposHom_structureMap`. -/
theorem ringedToposHom_structureMap_eq :
    (ringedToposHom τ f).structureMap =
      @RingedSite.ToposHom.Direct.inverseStructureMap
        (ringedSite τ T) (ringedSite τ S) _ _
        (ringedToposHom_toToposVal τ f)
        ((Over.map f).sheafPushforwardCocontinuous RingCat.{u}
          (τ.overTopology T) (τ.overTopology S))
        (ringedToposHom_forgetIso τ f)
        (ringedToposHom_structureMap τ f)
        (ringedToposHom_isRingCompatible τ f) :=
  rfl

end RingedToposHom

end AlgebraicGeometry.StandardTopology.Big

