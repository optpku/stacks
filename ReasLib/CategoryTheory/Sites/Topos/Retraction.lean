/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Retractions from continuous and cocontinuous site functors

This leaf records the topos-level retraction supplied by a fully faithful site
functor that is both continuous and cocontinuous, together with its localized
form on over-categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe w vC vD uC uD

namespace CategoryTheory.Functor

namespace Retraction

/-- The composite inverse image of the continuous and cocontinuous morphisms of topoi attached
to a fully faithful functor of sites is naturally isomorphic to the identity. -/
noncomputable def compInverseImageIso
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D)
    [u.Full] [u.Faithful]
    [u.IsContinuous J K] [u.IsCocontinuous J K]
    [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type w) J K)]
    [HasSheafify J (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        (u.morphismOfTopoiInOfContinuous J K)
        (u.morphismOfTopoiInOfCocontinuous J K)).inverseImage ≅
      (MorphismOfTopoiIn.id J).inverseImage :=
  Functor.isoWhiskerLeft (u.sheafPullback (Type w) J K)
      (@asIso _ _ _ _ (CocontinuousPullback.comparison.{w} u J K)
        (CocontinuousPullback.comparison.isIso.{w} u J K)) ≪≫
    (asIso (u.sheafAdjunctionContinuous (Type w) J K).unit).symm

/-- For a functor induced on over-categories, the composite inverse image of the continuous and
cocontinuous morphisms of topoi is naturally isomorphic to the identity. -/
noncomputable def overCompInverseImageIso
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) (X : C)
    [(Over.post (X := X) u).Full]
    [(Over.post (X := X) u).Faithful]
    [(Over.post (X := X) u).IsContinuous (J.over X) (K.over (u.obj X))]
    [(Over.post (X := X) u).IsCocontinuous (J.over X) (K.over (u.obj X))]
    [HasWeakSheafify (K.over (u.obj X)) (Type w)]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w, (Over.post (X := X) u).op.HasLeftKanExtension P]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w,
      (Over.post (X := X) u).op.HasPointwiseLeftKanExtension P]
    [PreservesFiniteLimits
      ((Over.post (X := X) u).sheafPullback (Type w) (J.over X) (K.over (u.obj X)))]
    [HasSheafify (J.over X) (Type w)]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w,
      (Over.post (X := X) u).op.HasPointwiseRightKanExtension P] :
    (MorphismOfTopoiIn.comp
        ((Over.post (X := X) u).morphismOfTopoiInOfContinuous
          (J.over X) (K.over (u.obj X)))
        ((Over.post (X := X) u).morphismOfTopoiInOfCocontinuous
          (J.over X) (K.over (u.obj X)))).inverseImage ≅
      (MorphismOfTopoiIn.id (J.over X)).inverseImage :=
  compInverseImageIso (J.over X) (K.over (u.obj X)) (Over.post (X := X) u)

end Retraction

end CategoryTheory.Functor
