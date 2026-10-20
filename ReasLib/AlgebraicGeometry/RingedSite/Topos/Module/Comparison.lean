module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction

/-!
# Composition and identity comparisons for module pullback
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor ComplexShape
open RingedSite
open Sheaf.InternalModule (underlyingApp)

noncomputable section

universe u v w uA vA

namespace CategoryTheory.SimplicialSites

variable {X Y Z : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (f : ToposHom X Y) (g : ToposHom Y Z) (h : ToposHom X Z)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (f.comp g).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{w} (ToposHom.id X).structureMap).IsRightAdjoint]
/-- Underlying type-valued sheaves identify the composite of module pushforwards along `f` and `g`
with module pushforward along `f.comp g`. -/
def modulePushforwardCompUnderlyingIso :
    (f.modulePushforward ⋙ g.modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying Z.structureSheaf ≅
      (f.comp g).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying Z.structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft f.modulePushforward (ToposHom.ModulePushforward.forgetIso g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ToposHom.ModulePushforward.forgetIso f) g.toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    (ToposHom.ModulePushforward.forgetIso (f.comp g)).symm

/-- The underlying pushforward comparison preserves addition of sections. -/
theorem modulePushforwardCompIso_add :
    ∀ M U (x y : ((f.modulePushforward ⋙ g.modulePushforward).obj M).val.obj U),
      underlyingApp (Z.structureSheaf) ((modulePushforwardCompUnderlyingIso f g).hom.app M) U (x + y) =
        underlyingApp (Z.structureSheaf) ((modulePushforwardCompUnderlyingIso f g).hom.app M) U x +
          underlyingApp (Z.structureSheaf) ((modulePushforwardCompUnderlyingIso f g).hom.app M) U y := sorry

/-- The underlying pushforward comparison preserves scalar multiplication of sections. -/
theorem modulePushforwardCompIso_smul :
    ∀ M U (a : (Z.structureSheaf).obj.obj U) (x : ((f.modulePushforward ⋙ g.modulePushforward).obj M).val.obj U),
      underlyingApp (Z.structureSheaf) ((modulePushforwardCompUnderlyingIso f g).hom.app M) U (a • x) =
        a • underlyingApp (Z.structureSheaf) ((modulePushforwardCompUnderlyingIso f g).hom.app M) U x := sorry

/-- Module pushforwards along `f` and `g` compose as `(f.comp g)_*`. -/
def modulePushforwardCompIso :
    f.modulePushforward ⋙ g.modulePushforward ≅ (f.comp g).modulePushforward :=
  Sheaf.InternalModule.functorIsoOfUnderlying _ (modulePushforwardCompUnderlyingIso f g) (modulePushforwardCompIso_add f g) (modulePushforwardCompIso_smul f g)

/-- Underived module pullbacks along `f` and `g` compose as `(f.comp g)^*`. -/
def modulePullbackCompIso :
    (f.comp g).modulePullback ≅ g.modulePullback ⋙ f.modulePullback :=
  (Adjunction.leftAdjointCompIso g.moduleAdjunction f.moduleAdjunction
      (f.comp g).moduleAdjunction (modulePushforwardCompIso f g)).symm

/-- Underlying type-valued sheaves identify module pushforward along `ToposHom.id` with the
identity. -/
def modulePushforwardIdUnderlyingIso :
    (ToposHom.id X).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying X.structureSheaf ≅
      𝟭 (SheafOfModules.{w} X.structureSheaf) ⋙
        Sheaf.InternalModule.ToInternal.underlying X.structureSheaf :=
  ToposHom.ModulePushforward.forgetIso (ToposHom.id X) ≪≫
    (Functor.rightUnitor _).symm

/-- The underlying pushforward comparison preserves addition of sections. -/
theorem modulePushforwardIdIso_add :
    ∀ M U (x y : (((ToposHom.id X).modulePushforward).obj M).val.obj U),
      underlyingApp (X.structureSheaf) ((modulePushforwardIdUnderlyingIso (X := X)).hom.app M) U (x + y) =
        underlyingApp (X.structureSheaf) ((modulePushforwardIdUnderlyingIso (X := X)).hom.app M) U x +
          underlyingApp (X.structureSheaf) ((modulePushforwardIdUnderlyingIso (X := X)).hom.app M) U y := sorry

/-- The underlying pushforward comparison preserves scalar multiplication of sections. -/
theorem modulePushforwardIdIso_smul :
    ∀ M U (a : (X.structureSheaf).obj.obj U) (x : (((ToposHom.id X).modulePushforward).obj M).val.obj U),
      underlyingApp (X.structureSheaf) ((modulePushforwardIdUnderlyingIso (X := X)).hom.app M) U (a • x) =
        a • underlyingApp (X.structureSheaf) ((modulePushforwardIdUnderlyingIso (X := X)).hom.app M) U x := sorry

/-- Module pushforward along `ToposHom.id` is the identity. -/
def modulePushforwardIdIso :
    (ToposHom.id X).modulePushforward ≅ 𝟭 (SheafOfModules.{w} X.structureSheaf) :=
  Sheaf.InternalModule.functorIsoOfUnderlying _ (modulePushforwardIdUnderlyingIso (X := X)) (modulePushforwardIdIso_add) (modulePushforwardIdIso_smul)

/-- Underived module pullback along `ToposHom.id` is the identity. -/
def modulePullbackIdIso :
    (ToposHom.id X).modulePullback ≅ 𝟭 (SheafOfModules.{w} X.structureSheaf) :=
  Adjunction.leftAdjointIdIso (ToposHom.id X).moduleAdjunction modulePushforwardIdIso

end CategoryTheory.SimplicialSites
