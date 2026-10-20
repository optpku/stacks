/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Topos.Retraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w vC vD uC uD

/-!
# Lemma 34.12.2

The source applies a site-theoretic retraction to five named big scheme
topologies.  The reusable statement is independent of that finite list and is
owned by `ReasLib.CategoryTheory.Sites.Topos.Retraction`.
-/

/- Lemma 34.12.2: the continuous and cocontinuous morphisms of topoi induced by a fully faithful
functor of sites compose to the identity up to natural isomorphism on inverse images. -/
@[stacks 022K] #check
  (@CategoryTheory.Functor.Retraction.compInverseImageIso :
    ∀ {C : Type uC} {D : Type uD}
      [Category.{vC} C] [Category.{vD} D]
      (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
      [u.Full] [u.Faithful]
      [u.IsContinuous J K] [u.IsCocontinuous J K]
      [HasWeakSheafify K (Type w)]
      [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
      [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseLeftKanExtension P]
      [PreservesFiniteLimits (u.sheafPullback (Type w) J K)]
      [HasSheafify J (Type w)]
      [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P],
      (MorphismOfTopoiIn.comp
          (u.morphismOfTopoiInOfContinuous J K)
          (u.morphismOfTopoiInOfCocontinuous J K)).inverseImage ≅
        (MorphismOfTopoiIn.id J).inverseImage)

#check
  (@CategoryTheory.Functor.Retraction.overCompInverseImageIso :
    ∀ {C : Type uC} {D : Type uD}
      [Category.{vC} C] [Category.{vD} D]
      (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (X : C)
      [(Over.post (X := X) u).Full]
      [(Over.post (X := X) u).Faithful]
      [(Over.post (X := X) u).IsContinuous (J.over X) (K.over (u.obj X))]
      [(Over.post (X := X) u).IsCocontinuous (J.over X) (K.over (u.obj X))]
      [HasWeakSheafify (K.over (u.obj X)) (Type w)]
      [∀ P : (Over X)ᵒᵖ ⥤ Type w,
        (Over.post (X := X) u).op.HasLeftKanExtension P]
      [∀ P : (Over X)ᵒᵖ ⥤ Type w,
        (Over.post (X := X) u).op.HasPointwiseLeftKanExtension P]
      [PreservesFiniteLimits
        ((Over.post (X := X) u).sheafPullback (Type w) (J.over X) (K.over (u.obj X)))]
      [HasSheafify (J.over X) (Type w)]
      [∀ P : (Over X)ᵒᵖ ⥤ Type w,
        (Over.post (X := X) u).op.HasPointwiseRightKanExtension P],
      (MorphismOfTopoiIn.comp
          ((Over.post (X := X) u).morphismOfTopoiInOfContinuous
            (J.over X) (K.over (u.obj X)))
          ((Over.post (X := X) u).morphismOfTopoiInOfCocontinuous
            (J.over X) (K.over (u.obj X)))).inverseImage ≅
        (MorphismOfTopoiIn.id (J.over X)).inverseImage)
