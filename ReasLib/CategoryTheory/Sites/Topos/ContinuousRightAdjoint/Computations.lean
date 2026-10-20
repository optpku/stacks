module

public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Objectwise direct-image computations for continuous right adjoints

This leaf exposes the objectwise form of the comparison between cocontinuous
direct image along a left adjoint and continuous direct image along its
continuous right adjoint.  Site-specific developments should use these
computations instead of rebuilding whiskered presheaf isomorphisms.
-/

@[expose] public section

open CategoryTheory
open Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace ContinuousRightAdjoint

/-- The value of the cocontinuous direct image along `u` is computed by
evaluation of the input sheaf on the continuous right adjoint `v`. -/
noncomputable def pushforwardCocontinuousObjObjIso
    (u : C ⥤ D) (v : D ⥤ C) (A : Type (w + 1)) [Category.{w} A]
    (adj : u ⊣ v)
    [v.IsContinuous K J]
    [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P]
    (F : Sheaf J A) (X : D) :
    (((u.sheafPushforwardCocontinuous A J K).obj F).obj.obj (op X)) ≅
      F.obj.obj (op (v.obj X)) :=
  let e :
      (((u.sheafPushforwardCocontinuous A J K).obj F).obj) ≅
        v.op ⋙ F.obj :=
    ((Functor.isoWhiskerRight
      (pushforwardContinuousIso u v A adj).symm
      (sheafToPresheaf K A)).app F) ≪≫
      ((v.sheafPushforwardContinuousCompSheafToPresheafIso A K J).app F)
  e.app (op X)

end ContinuousRightAdjoint

end CategoryTheory.Functor
