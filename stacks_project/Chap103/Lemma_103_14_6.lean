/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap96.Lemma_96_12_4_LQCoh
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap103.Definition_103_9_1_Parasitic
public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Parasitic
import StacksCheckRecall

/-!
# Parasitic modules via lisse-étale and flat-fppf pullback

On an algebraic stack, parasitic vanishing of an étale module with the flat
base change property is equivalent to vanishing after pullback along the
lisse-étale ringed morphism of Lemma 103.14.2, and parasitic vanishing of an
fppf module is equivalent to vanishing after pullback along the flat-fppf
ringed morphism. The explicit existence premises express a bounded-site size
convention.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/- Lemma 103.14.6 (1): parasitic vanishing is equivalent to zero
lisseEtale module pullback, under the bounded-site existence premises. -/
@[stacks 07AR] #check (AlgebraicGeometry.AlgebraicStack.isParasitic_iff_lisseEtaleModulePullback_isZero :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (F : etaleModules X)
    [HasFlatBaseChange F],
    IsParasitic (etaleModulePresheaf F) ↔
      IsZero ((lisseEtaleModulePullback X).obj F))

/- Lemma 103.14.6 (2): parasitic vanishing is equivalent to zero
flatFppf module pullback, under the bounded-site existence premises. -/
@[stacks 07AR] #check (AlgebraicGeometry.AlgebraicStack.isParasitic_iff_flatFppfModulePullback_isZero :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (F : SheafOfModules.{u} (structureSheaf X)),
    IsParasitic F.val ↔
      IsZero ((flatFppfModulePullback X).obj F))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModulePullback_isZero_of_isParasitic :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (F : etaleModules X)
    [HasFlatBaseChange F],
    IsParasitic (etaleModulePresheaf F) →
      IsZero ((lisseEtaleModulePullback X).obj F))

#check (AlgebraicGeometry.AlgebraicStack.isParasitic_of_lisseEtaleModulePullback_isZero :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (F : etaleModules X)
    [HasFlatBaseChange F],
    IsZero ((lisseEtaleModulePullback X).obj F) →
      IsParasitic (etaleModulePresheaf F))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModulePullback_isZero_of_isParasitic :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (F : SheafOfModules.{u} (structureSheaf X)),
    IsParasitic F.val →
      IsZero ((flatFppfModulePullback X).obj F))

#check (AlgebraicGeometry.AlgebraicStack.isParasitic_of_flatFppfModulePullback_isZero :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (F : SheafOfModules.{u} (structureSheaf X)),
    IsZero ((flatFppfModulePullback X).obj F) →
      IsParasitic F.val)

end AlgebraicGeometry.AlgebraicStack
