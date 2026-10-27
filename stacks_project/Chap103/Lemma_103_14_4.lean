/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.ModuleLowerShriek
public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek
import StacksCheckRecall

/-!
On an algebraic stack, module lower shriek along the lisse-étale and
flat-fppf inclusions is left adjoint to restriction, agrees with abelian
lower shriek, and satisfies `g^* g_! = id`. The abelian comparison premises
express the bounded-site size convention.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/- Lemma 103.14.4 (1): there is a functor
g_! : Mod(X_lisse,étale, 𝒪) ⟶ Mod(X_étale, 𝒪_X). -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    SheafOfModules.{u} (lisseEtaleStructureSheaf X) ⥤
      SheafOfModules.{u} (etaleStructureSheaf X))

/- Lemma 103.14.4 (2): lisse-étale module lower shriek is left adjoint to g^*. -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    lisseEtaleModuleLowerShriek X ⊣ lisseEtaleModuleInverseImage X)

/- Lemma 103.14.4 (3): lisse-étale module lower shriek agrees with abelian g_!. -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.underlyingComparison_isIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (lisseEtaleInclusion X).op.HasLeftKanExtension P],
    IsIso (lisseEtaleModuleLowerShriek.underlyingComparison X))

/- Lemma 103.14.4 (4): g^* g_! = id on lisse-étale modules. -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek_unit_app_isIso :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X] (F : SheafOfModules.{u} (lisseEtaleStructureSheaf X)),
    IsIso ((lisseEtaleModuleLowerShriek.adjunction X).unit.app F))

/- Lemma 103.14.4 (5): there is a functor
g_! : Mod(X_flat,fppf, 𝒪) ⟶ Mod(X_fppf, 𝒪_X). -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    SheafOfModules.{u} (flatFppfStructureSheaf X) ⥤
      SheafOfModules.{u} (structureSheaf X))

/- Lemma 103.14.4 (6): flat-fppf module lower shriek is left adjoint to g^*. -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.adjunction :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X],
    flatFppfModuleLowerShriek X ⊣ flatFppfModuleInverseImage X)

/- Lemma 103.14.4 (7): flat-fppf module lower shriek agrees with abelian g_!. -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.underlyingComparison_isIso :
  ∀ (X : GroupoidsOver S) [AlgebraicStack X]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u}]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (flatFppfInclusion X).op.HasLeftKanExtension P],
    IsIso (flatFppfModuleLowerShriek.underlyingComparison X))

/- Lemma 103.14.4 (8): g^* g_! = id on flat-fppf modules. -/
@[stacks 0789]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek_unit_app_isIso :
  ∀ (X : GroupoidsOver S)
    [AlgebraicStack X] (F : SheafOfModules.{u} (flatFppfStructureSheaf X)),
    IsIso ((flatFppfModuleLowerShriek.adjunction X).unit.app F))

end AlgebraicGeometry.AlgebraicStack
