/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Ringed
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Parasitic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent

/-!
# Parasitic modules and restriction to smooth or flat objects

Parasitic vanishing is characterized by zero module pullback to the
lisse-étale or flat-fppf site. In the étale case, flat base change is required.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- An étale module with flat base change is parasitic if and only if its
lisse-étale module pullback is zero.
The existence premises express a bounded-site size convention. -/
theorem isParasitic_iff_lisseEtaleModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (F : etaleModules X)
    [HasFlatBaseChange F] :
    IsParasitic (etaleModulePresheaf F) ↔
      IsZero ((lisseEtaleModulePullback X).obj F) :=
  sorry

/-- An fppf module is parasitic if and only if its flat-fppf module pullback
is zero.
The existence premises express a bounded-site size convention. -/
theorem isParasitic_iff_flatFppfModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    IsParasitic F.val ↔
      IsZero ((flatFppfModulePullback X).obj F) :=
  sorry

/-- The lisse-étale module pullback of a parasitic étale module with flat
base change is zero.
The existence premises express a bounded-site size convention. -/
theorem lisseEtaleModulePullback_isZero_of_isParasitic
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (F : etaleModules X)
    [HasFlatBaseChange F] :
    IsParasitic (etaleModulePresheaf F) →
      IsZero ((lisseEtaleModulePullback X).obj F) :=
  sorry

/-- An étale module with flat base change is parasitic if its lisse-étale
module pullback is zero.
The existence premises express a bounded-site size convention. -/
theorem isParasitic_of_lisseEtaleModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u,
      (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.etaleTopology (Type u)]
    (F : etaleModules X)
    [HasFlatBaseChange F] :
    IsZero ((lisseEtaleModulePullback X).obj F) →
      IsParasitic (etaleModulePresheaf F) :=
  sorry

/-- The flat-fppf module pullback of a parasitic fppf module is zero.
The existence premises express a bounded-site size convention. -/
theorem flatFppfModulePullback_isZero_of_isParasitic
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    IsParasitic F.val →
      IsZero ((flatFppfModulePullback X).obj F) :=
  sorry

/-- An fppf module is parasitic if its flat-fppf module pullback is zero.
The existence premises express a bounded-site size convention. -/
theorem isParasitic_of_flatFppfModulePullback_isZero
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u,
      (flatFppfInclusion X).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    (F : SheafOfModules.{u} (structureSheaf X)) :
    IsZero ((flatFppfModulePullback X).obj F) →
      IsParasitic F.val :=
  sorry

end AlgebraicGeometry.AlgebraicStack
