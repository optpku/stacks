/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.RingedTopos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.Small
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open AlgebraicGeometry.StandardTopology.Big

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale.Module

variable {S T : Scheme.{u}}

/-- The scheme-valued projection from a small étale pullback to its base object. -/
noncomputable def smallProjection (f : T ⟶ S) :
    (smallEtalePullback f ⋙ Scheme.smallEtaleToScheme T) ⟶ Scheme.smallEtaleToScheme S where
  app U := pullback.fst U.hom f
  naturality := by intros; sorry

/-- The structure-sheaf map induced by the projections of a small étale fibre product. -/
noncomputable def smallStructureSheafMap (f : T ⟶ S) :
    Small.structureSheaf S ⟶
      (smallEtalePullback f).sheafPushforwardContinuous RingCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology |>.obj (Small.structureSheaf T) :=
  Scheme.Site.structureSheafMap S.smallEtaleTopology T.smallEtaleTopology
    (Scheme.smallEtaleToScheme S) (Scheme.smallEtaleToScheme T) (smallEtalePullback f)
    (smallProjection f) (Small.structurePresheaf_isSheaf S)
    (Small.structurePresheaf_isSheaf T)

/-- The module-sheaf direct image on the small étale sites of a scheme morphism. -/
noncomputable def smallDirectImage (f : T ⟶ S) :
    SheafOfModules.{v} (Small.structureSheaf T) ⥤
      SheafOfModules.{v} (Small.structureSheaf S) :=
  SheafOfModules.pushforward (smallStructureSheafMap f)

/-- The small direct image is computed by fibre-product evaluation and restriction of scalars. -/
theorem smallDirectImage_obj (f : T ⟶ S)
    (M : SheafOfModules.{v} (Small.structureSheaf T)) (U : S.Etale) :
    ((smallDirectImage.{u, v} f).obj M).val.obj (op U) =
      (ModuleCat.restrictScalars ((smallStructureSheafMap f).hom.app (op U)).hom).obj
        (M.val.obj (op ((smallEtalePullback f).obj U))) := sorry

/-- The scheme-valued projection from a big étale pullback to its base object. -/
noncomputable def bigProjection (f : T ⟶ S) :
    (Over.pullback f ⋙ Over.forget T) ⟶ Over.forget S where
  app U := pullback.fst U.hom f
  naturality := by intros; sorry

/-- The structure-sheaf map induced by the projections of a big étale fibre product. -/
noncomputable def bigStructureSheafMap (f : T ⟶ S) :
    StandardTopology.Big.structureSheaf .etale S ⟶
      (Over.pullback f).sheafPushforwardContinuous RingCat.{u}
        (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale) |>.obj
          (StandardTopology.Big.structureSheaf .etale T) :=
  Scheme.Site.structureSheafMap (S.overGrothendieckTopology @Etale)
    (T.overGrothendieckTopology @Etale) (Over.forget S) (Over.forget T) (Over.pullback f)
    (bigProjection f) (StandardTopology.Big.structurePresheaf_isSheaf .etale S)
    (StandardTopology.Big.structurePresheaf_isSheaf .etale T)

/-- The module-sheaf direct image on the big étale sites of a scheme morphism. -/
noncomputable def bigDirectImage (f : T ⟶ S) :
    SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T) ⥤
      SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S) :=
  SheafOfModules.pushforward (bigStructureSheafMap f)

/-- The big direct image is computed by fibre-product evaluation and restriction of scalars. -/
theorem bigDirectImage_obj (f : T ⟶ S)
    (M : SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T)) (U : Over S) :
    ((bigDirectImage.{u, v} f).obj M).val.obj (op U) =
      (ModuleCat.restrictScalars ((bigStructureSheafMap f).hom.app (op U)).hom).obj
        (M.val.obj (op ((Over.pullback f).obj U))) := sorry

/-- Exact module restriction from the big étale site of `S` to the small étale site of `T`. -/
noncomputable def relocalization (f : T ⟶ S) :
    SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S) ⥤
      SheafOfModules.{v} (Small.structureSheaf T) :=
  SheafOfModules.pushforward.{v} (F := relocalizationFunctor f)
    (S := Small.structureSheaf T) (R := StandardTopology.Big.structureSheaf .etale S)
    (SmallToBig.inverseImageStructureMap f)

/-- Relocalization evaluates a big module sheaf on the same scheme over the base. -/
theorem relocalization_obj (f : T ⟶ S)
    (M : SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S)) (U : T.Etale) :
    ((relocalization.{u, v} f).obj M).val.obj (op U) =
      (ModuleCat.restrictScalars ((SmallToBig.inverseImageStructureMap f).hom.app (op U)).hom).obj
        (M.val.obj (op ((relocalizationFunctor f).obj U))) := sorry

/-- The big-site structure-sheaf map for postcomposition along a scheme morphism. -/
noncomputable def bigInverseStructureSheafMap (f : T ⟶ S) :
    StandardTopology.Big.structureSheaf .etale T ⟶
      (Over.map f).sheafPushforwardContinuous RingCat.{u}
        (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale) |>.obj
          (StandardTopology.Big.structureSheaf .etale S) :=
  Scheme.Site.structureSheafMap (T.overGrothendieckTopology @Etale)
    (S.overGrothendieckTopology @Etale) (Over.forget T) (Over.forget S) (Over.map f)
    (Over.mapForget f).hom (StandardTopology.Big.structurePresheaf_isSheaf .etale T)
    (StandardTopology.Big.structurePresheaf_isSheaf .etale S)

/-- Exact inverse image on big étale module sheaves induced by postcomposition. -/
noncomputable def bigInverseImage (f : T ⟶ S) :
    SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S) ⥤
      SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale T) :=
  SheafOfModules.pushforward (bigInverseStructureSheafMap f)

/-- Big inverse image is computed by evaluation after postcomposition. -/
theorem bigInverseImage_obj (f : T ⟶ S)
    (M : SheafOfModules.{v} (StandardTopology.Big.structureSheaf .etale S)) (U : Over T) :
    ((bigInverseImage.{u, v} f).obj M).val.obj (op U) =
      (ModuleCat.restrictScalars ((bigInverseStructureSheafMap f).hom.app (op U)).hom).obj
        (M.val.obj (op ((Over.map f).obj U))) := sorry

end AlgebraicGeometry.Scheme.Etale.Module

end
