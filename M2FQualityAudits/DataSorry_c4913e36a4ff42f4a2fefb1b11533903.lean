/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Lean

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sections.Chaotic
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived modules on a category with the chaotic topology

This leaf owns the canonical section and restriction functors used to specialize the
comparison-defined quasi-coherent subcategory to a sheaf of rings on the chaotic site.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open SheafOfModules.RingedSite

universe u v w

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]

/-- Sections at `U` for modules over a sheaf of rings on the chaotic site. -/
@[stacks 0GYV "chaotic-site sections"]
abbrev chaoticSections (U : C) :
    ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) 𝒪 ⥤
      ModuleCat.{max (max u v) w} (𝒪.1.obj (op U)) :=
  SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U)

/-- Evaluation at `U` on the chaotic site, bundled as an exact functor. -/
@[stacks 0GYV "exact chaotic-site sections"]
noncomputable def chaoticSectionsExact (U : C) :
    ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
        (⊥ : GrothendieckTopology C) 𝒪 ⥤ₑ
      ModuleCat.{max (max u v) w} (𝒪.1.obj (op U)) :=
  ⟨SheafOfModules.RingedSite.BaseChange.evaluation 𝒪 U,
    SheafOfModules.RingedSite.Chaotic.BaseChange.evaluation_exact 𝒪 U⟩

section Derived

/-- The canonical derived sections functor at `U` on the chaotic site. Since evaluation is
exact, the direct `mapDerivedCategory` presentation is the primary owner. -/
@[stacks 0GYV "chaotic-site derived sections"]
noncomputable abbrev chaoticRGamma (U : C) :
    RingedSite.Hom.ModuleDerived.{max (max u v) w}
        (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪) ⥤
      DerivedCategory (ModuleCat.{max (max u v) w} (𝒪.1.obj (op U))) :=
  @Functor.mapDerivedCategory
    (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) 𝒪) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪))
    _ inferInstance inferInstance inferInstance
    (chaoticSectionsExact 𝒪 U).obj inferInstance inferInstance inferInstance

/-- The total-right-derived presentation of exact chaotic-site evaluation. -/
@[stacks 0GYV "homotopy total-right-derived chaotic sections"]
noncomputable abbrev chaoticRGammaHomotopy (U : C) :
    RingedSite.Hom.ModuleDerived.{max (max u v) w}
        (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪) ⥤
      DerivedCategory (ModuleCat.{max (max u v) w} (𝒪.1.obj (op U))) :=
  @Functor.RightDerived.Homotopy.functor
    (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) 𝒪) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪))
    _ inferInstance inferInstance inferInstance
    (chaoticSectionsExact 𝒪 U).obj inferInstance inferInstance

/-- Exact and total-right-derived presentations of chaotic-site evaluation are canonically
isomorphic. -/
@[stacks 0GYV "derived sections presentation comparison"]
noncomputable def chaoticRGammaIso (U : C) :
    chaoticRGamma 𝒪 U ≅ chaoticRGammaHomotopy 𝒪 U :=
  @Functor.RightDerived.Exact.homotopyIso
    (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) 𝒪) inferInstance inferInstance
    _ inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪))
    inferInstance (chaoticSectionsExact 𝒪 U).obj inferInstance inferInstance inferInstance

/-- For `f : U ⟶ V`, derived restriction on the chaotic site is extension of scalars along
`𝒪(V) ⟶ 𝒪(U)`. -/
@[stacks 0GYV "chaotic-site derived restriction"]
abbrev chaoticDerivedRestrict {U V : C} (f : U ⟶ V) :
    DerivedCategory (ModuleCat.{max (max u v) w} (𝒪.1.obj (op V))) ⥤
      DerivedCategory (ModuleCat.{max (max u v) w} (𝒪.1.obj (op U))) :=
  ModuleCat.derivedExtensionOfScalars ((𝒪.1.map f.op).hom)

/-- The canonical derived base-change map
`RΓ(V, K) ⊗ᴸ[𝒪(V)] 𝒪(U) ⟶ RΓ(U, K)` associated to `f : U ⟶ V`. -/
@[stacks 0GYV "canonical derived base-change comparison"]
noncomputable def chaoticComparison {U V : C} (f : U ⟶ V) :
    chaoticRGamma 𝒪 V ⋙ chaoticDerivedRestrict 𝒪 f ⟶ chaoticRGamma 𝒪 U :=
  @Functor.LeftDerived.Homotopy.Composition.ExactFirst.comparison
    (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) 𝒪) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪))
    (ModuleCat.{max (max u v) w} (𝒪.1.obj (op V))) inferInstance inferInstance inferInstance
    (ModuleCat.{max (max u v) w} (𝒪.1.obj (op U))) inferInstance inferInstance inferInstance
    (chaoticSectionsExact 𝒪 V) (ModuleCat.extendScalars ((𝒪.1.map f.op).hom))
    (chaoticSectionsExact 𝒪 U) inferInstance inferInstance
    (SheafOfModules.RingedSite.BaseChange.natTrans 𝒪 f)

/-- The canonical chaotic-site derived base-change comparison is obtained by descending its
explicit homotopy-level comparison. -/
@[stacks 0GYV "canonical derived base-change localization equation"]
theorem chaoticComparison_fac {U V : C} (f : U ⟶ V) :
    Functor.whiskerLeft
        (RingedSite.Hom.moduleLocalization.{max (max u v) w}
          (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪))
        (chaoticComparison 𝒪 f) =
      @Functor.LeftDerived.Homotopy.Composition.ExactFirst.comparisonOnHomotopy
        (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
          (⊥ : GrothendieckTopology C) 𝒪) inferInstance inferInstance
        (RingedSite.Hom.moduleCat_hasDerivedCategory
          (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪))
        (ModuleCat.{max (max u v) w} (𝒪.1.obj (op V))) inferInstance inferInstance inferInstance
        (ModuleCat.{max (max u v) w} (𝒪.1.obj (op U))) inferInstance inferInstance inferInstance
        (chaoticSectionsExact 𝒪 V) (ModuleCat.extendScalars ((𝒪.1.map f.op).hom))
        (chaoticSectionsExact 𝒪 U) inferInstance inferInstance
        (SheafOfModules.RingedSite.BaseChange.natTrans 𝒪 f) := sorry

end Derived

namespace Chaotic

/-- The canonical quasi-coherence property for derived modules on the chaotic ringed site. -/
@[stacks 0GYV "canonical quasi-coherence property"]
abbrev isQuasiCoherent : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{max (max u v) w}
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪)) :=
  ModulesOnCategory.isQuasiCoherent 𝒪.1 (chaoticRGamma 𝒪)
    (chaoticDerivedRestrict 𝒪) (chaoticComparison 𝒪)

/-- The full subcategory of canonically quasi-coherent derived modules on a category equipped
with the chaotic topology. -/
@[stacks 0GYV "canonical quasi-coherent derived-module subcategory"]
abbrev QC := (isQuasiCoherent 𝒪).FullSubcategory

/-- Membership in `Chaotic.QC 𝒪` is invertibility of every canonical derived base-change
comparison. -/
@[simp, stacks 0GYV "canonical quasi-coherence membership"]
theorem mem_iff (K : RingedSite.Hom.ModuleDerived.{max (max u v) w}
    (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) 𝒪)) :
    isQuasiCoherent 𝒪 K ↔
      ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((chaoticComparison 𝒪 f).app K) := sorry

/-- Every canonical derived base-change map of an object of `Chaotic.QC 𝒪` is an
isomorphism. -/
@[stacks 0GYV "canonical quasi-coherent comparison isomorphism"]
theorem comparison_isIso (K : QC 𝒪) {U V : C} (f : U ⟶ V) :
    IsIso ((chaoticComparison 𝒪 f).app K.obj) := sorry

end Chaotic

end CategoryTheory.ModulesOnCategory


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
