/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap96.Lemma_96_10_1_Comparison

/-!
# Restriction of étale modules to a representing algebraic space

An equivalence `e : U.toGroupoids ≌ X` induces the morphism of ringed sites
`π_U : (X_étale, 𝒪_X) ⟶ (U_étale, 𝒪_U)`. Restriction of an étale sheaf of
`𝒪_X`-modules to `U_étale` is module pushforward along `π_U`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open FiberedCategoryOver.Groupoids
open RingedSite.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Ring-valued sheaves on the associated étale topology of a category fibred in
groupoids compose with the forgetful functor to types. -/
instance etaleTopology_hasSheafCompose (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- Module pushforward along `π_U` is a right adjoint, as required to compare it
with inverse image along `i_U`. -/
instance pi_modulePushforward_isRightAdjoint {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X) :
    ((pi U X e).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Restriction of an étale sheaf of `𝒪_X`-modules to the small étale site of a
representing algebraic space `U`, as `F |_{U_étale} = π_{U,*} F`. -/
def restrictModules {U : AlgebraicSpace S} {X : GroupoidsOver S} (e : U.toGroupoids ≌ X) :
    SheafOfModules.{u} (etaleRingedSite X).structureSheaf ⥤
      SheafOfModules.{u} (AlgebraicSpace.structureSheaf U) :=
  (pi U X e).modulePushforward.{u}

/-- `restrictModules e` is module pushforward along `π_U`. -/
theorem restrictModules_eq {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X) :
    restrictModules e = (pi U X e).modulePushforward.{u} :=
  rfl

/-- Sections of a restricted module sheaf over `W` étale over `U` are the original
sections on `u(W)`, after restriction of scalars along the structure-sheaf map
of `π_U`. -/
theorem restrictModules_obj {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X)
    (F : SheafOfModules.{u} (etaleRingedSite X).structureSheaf)
    (W : AlgebraicSpace.smallEtaleSite U) :
    ((restrictModules e).obj F).val.obj (op W) =
      (ModuleCat.restrictScalars ((pi U X e).structureSheafMap.hom.app (op W)).hom).obj
        (F.val.obj (op ((smallEtaleFunctor U X e).obj W))) :=
  sorry

/-- Restriction along `π_U` agrees with inverse image along `i_U`, i.e.
`π_{U,*} F = i_U⁻¹ F` on étale modules. -/
theorem restrictModules_eq_inclusion {U : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : U.toGroupoids ≌ X)
    [HasSheafify (AlgebraicSpace.smallEtaleTopology U) (Type u)]
    [∀ P : (AlgebraicSpace.smallEtaleSite U)ᵒᵖ ⥤ Type u,
      (smallEtaleFunctor U X e).op.HasPointwiseRightKanExtension P]
    [∀ P : (AlgebraicSpace.smallEtaleSite U)ᵒᵖ ⥤ RingCat.{u},
      (smallEtaleFunctor U X e).op.HasPointwiseRightKanExtension P]
    [(AlgebraicSpace.smallEtaleTopology U).HasSheafCompose (forget RingCat.{u})]
    [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor U X e).op]
    [(SheafOfModules.restrictScalars.{u}
        (inclusion U X e).structureMap).IsRightAdjoint] :
    restrictModules e = (inclusion U X e).modulePullback :=
  sorry

end AlgebraicGeometry.GroupoidsOver
