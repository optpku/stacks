/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint

/-!
# Pullback of a continuous functor with a left adjoint

This module owns the reusable comparisons for the lower-shriek functor attached to a continuous
functor of sites which has a left adjoint.  The presheaf Kan-extension comparison and the
sheafification comparison are exposed separately, so later constructions can use either layer
without depending on the Chapter 7 compatibility module.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe t u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace Functor.LeftAdjoint

/-- An adjunction `w ⊣ u` identifies precomposition along `w.op` with the left Kan extension
along `u.op`. -/
noncomputable def opWhiskeringIsoLan
    (u : C ⥤ D) (w : D ⥤ C) (adj : w ⊣ u)
    (A : Type (t + 1)) [Category.{t} A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P] :
    (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj w.op ≅ u.op.lan :=
  (adj.op.whiskerLeft A).leftAdjointUniq (u.op.lanAdjunction A)

/-- The sheafified pullback along a left adjoint is the Kan-extension pullback construction for
its right adjoint. -/
noncomputable def pullbackCocontinuousIsoConstruction
    (u : C ⥤ D) (w : D ⥤ C) (adj : w ⊣ u)
    (A : Type (t + 1)) [Category.{t} A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [HasWeakSheafify K A] :
    w.sheafPullbackCocontinuous A K J ≅
      Functor.sheafPullbackConstruction.sheafPullback u A J K := by
  simpa [Functor.sheafPullbackCocontinuous,
    Functor.sheafPullbackConstruction.sheafPullback] using
    Functor.isoWhiskerLeft (sheafToPresheaf J A)
      (Functor.isoWhiskerRight (opWhiskeringIsoLan u w adj A) (presheafToSheaf K A))

section LeftKanExtension

/-- If `w ⊣ u`, the lower-shriek functor attached to the
continuous functor `u` is canonically the sheafified pullback along `w`. -/
@[stacks 08NH "(1)"]
noncomputable def pullbackIsoCocontinuous
    (u : C ⥤ D) (w : D ⥤ C) (adj : w ⊣ u)
    [u.IsContinuous J K]
    (A : Type (t + 1)) [Category.{t} A]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension P]
    [HasWeakSheafify K A] :
    u.sheafPullback A J K ≅ w.sheafPullbackCocontinuous A K J :=
  Functor.sheafPullbackConstruction.sheafPullbackIso u A J K ≪≫
    (Functor.LeftAdjoint.pullbackCocontinuousIsoConstruction u w adj A).symm

/-- The lower-shriek functor attached to a continuous functor with
a left adjoint is exact. -/
@[stacks 08NH "(2)"]
theorem pullbackExact
    (u : C ⥤ D) (w : D ⥤ C) (adj : w ⊣ u)
    [u.IsContinuous J K]
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P]
    [HasSheafify K (Type t)] :
    exactFunctor (Sheaf J (Type t)) (Sheaf K (Type t)) (u.sheafPullback (Type t) J K) := sorry

end LeftKanExtension

end Functor.LeftAdjoint

namespace Functor.ContinuousLeftAdjoint

/-- The canonical comparison used to transport a right-adjoint structure from the continuous
direct image induced by `w` to the lower-shriek functor induced by `u`. -/
noncomputable def pullbackIsoPushforward
    (u : C ⥤ D) (w : D ⥤ C) (adj : w ⊣ u)
    [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous (Type t) J K).IsRightAdjoint]
    [w.IsContinuous K J] :
    u.sheafPullback (Type t) J K ≅ w.sheafPushforwardContinuous (Type t) K J :=
  Adjunction.leftAdjointUniq
    (u.sheafAdjunctionContinuous (Type t) J K)
    (Adjunction.sheafPushforwardContinuous adj K J)

/-- A lower-shriek functor is a right adjoint whenever the
identified continuous direct-image functor is a right adjoint. -/
@[stacks 08NH "(3)"]
theorem pullbackIsRightAdjoint
    (u : C ⥤ D) (w : D ⥤ C) (adj : w ⊣ u)
    [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous (Type t) J K).IsRightAdjoint]
    [w.IsContinuous K J]
    [(w.sheafPushforwardContinuous (Type t) K J).IsRightAdjoint] :
    (u.sheafPullback (Type t) J K).IsRightAdjoint := sorry

end Functor.ContinuousLeftAdjoint

namespace Functor.CocontinuousLeftAdjoint

/-- When the left adjoint `w` is cocontinuous, the lower-shriek
functor attached to `u` is canonically the inverse-image functor of the induced morphism of
topoi. -/
@[stacks 08NH "(4)"]
noncomputable def pullbackIsoInverseImage
    (u : C ⥤ D) (w : D ⥤ C) (adj : w ⊣ u)
    [u.IsContinuous J K]
    [w.IsCocontinuous K J]
    [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P]
    [HasSheafify K (Type t)]
    [∀ P : Dᵒᵖ ⥤ Type t, w.op.HasPointwiseRightKanExtension P] :
    u.sheafPullback (Type t) J K ≅
      (w.morphismOfTopoiInOfCocontinuous K J).inverseImage := by
  simpa only [Functor.morphismOfTopoiInOfCocontinuous_inverseImage] using
    Functor.LeftAdjoint.pullbackIsoCocontinuous u w adj (Type t)

end Functor.CocontinuousLeftAdjoint

end CategoryTheory
