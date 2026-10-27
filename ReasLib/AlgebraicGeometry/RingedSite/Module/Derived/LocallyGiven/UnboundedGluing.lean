/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven.Gluing
public import ReasLib.AlgebraicGeometry.RingedSite.FiberwiseSerre

/-!
# Unbounded gluing of locally given derived modules

Local derived modules with cohomology in a fiberwise weak Serre family glue
uniquely when negative self-Exts vanish and their indexing category covers an
auxiliary site whose functor preserves equalizers and pullbacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom RingedSite.Localization
open RingedSite.ModuleDerived
open scoped SemiRepresentableFamily

noncomputable section

universe ιfam wι u v w uB vB u' v'

namespace RingedSite.ModuleDerived.LocallyGiven

variable {X : RingedSite.{u, v, w}}
variable {B : Type uB} [Category.{vB} B]
variable [UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ {U V : X} (f : V ⟶ U),
    (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]

/-- A locally given datum has cohomology in a fiberwise weak Serre family when
each `E_U` has cohomology in `A.property` at `u(U)`. -/
def obj_mem_cohomologyIn (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
    (A : FiberwiseSerre.{wι, u, v, w} X) : Prop :=
  ∀ (U : B) (n : ℤ),
    A.property (D.u.obj U) ((DerivedCategory.homologyFunctor _ n).obj (D.obj U))

/-- Unfolding of cohomology-in membership for a locally given datum. -/
theorem obj_mem_cohomologyIn_iff (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
    (A : FiberwiseSerre.{wι, u, v, w} X) :
    obj_mem_cohomologyIn D A ↔
      ∀ (U : B) (n : ℤ),
        A.property (D.u.obj U) ((DerivedCategory.homologyFunctor _ n).obj (D.obj U)) :=
  sorry

end RingedSite.ModuleDerived.LocallyGiven

namespace RingedSite.ModuleDerived.LocallyGiven

variable {X : RingedSite.{u, v, w}}
variable [h_eqX : HasEqualizers X.carrier] [h_pbX : HasPullbacks X.carrier]
variable {B : Type uB} [Category.{vB} B]
variable [h_univLE : UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ {U V : X} (f : V ⟶ U),
    (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]
variable (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
variable {C' : Type u'} [Category.{v'} C']
variable [h_eqC : HasEqualizers C'] [h_pbC : HasPullbacks C']
variable (J' : GrothendieckTopology C') (u' : C' ⥤ X)
variable [h_sites : IsMorphismOfSites J' X.siteTopology u']
variable [h_eqPres : PreservesLimitsOfShape WalkingParallelPair u']
variable [h_pbPres : PreservesLimitsOfShape WalkingCospan u']
variable (ι : B ⥤ C') [h_full : ι.Full] [h_faithful : ι.Faithful]
variable (A : FiberwiseSerre.{wι, u, v, w} X)
include h_eqX h_pbX h_eqC h_pbC h_sites h_eqPres h_pbPres h_full h_faithful

/-- Locally given derived modules with vanishing negative self-Exts and
cohomology in a fiberwise weak Serre family admit a global solution when their
indexing category embeds fully faithfully as a covering basis in an auxiliary
site whose functor defines a morphism of sites and preserves equalizers and
pullbacks, with both sites admitting these limits. -/
@[stacks 0DCC]
theorem exists_solution_of_cohomologyIn
    (h_restrict : D.u = ι ⋙ u')
    (h_cover : ∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj))
    (h_neg : negativeSelfExt h_univLE D)
    (h_mem : obj_mem_cohomologyIn D A) :
    Nonempty (Solution D) :=
  sorry

/-- Any two solutions of locally given derived modules with vanishing negative
self-Exts and cohomology in a fiberwise weak Serre family admit a unique
compatible isomorphism when the indexing category embeds fully faithfully as a
covering basis in an auxiliary site whose functor defines a morphism of sites
and preserves equalizers and pullbacks, with both sites admitting these limits. -/
@[stacks 0DCC]
theorem unique_hom_solution_of_cohomologyIn
    (h_restrict : D.u = ι ⋙ u')
    (h_cover : ∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj))
    (h_neg : negativeSelfExt h_univLE D)
    (h_mem : obj_mem_cohomologyIn D A)
    (S S' : Solution D) :
    ∃ e : S.obj ≅ S'.obj,
      Solution.IsCompatibleIso S S' e ∧
        ∀ e' : S.obj ≅ S'.obj, Solution.IsCompatibleIso S S' e' → e'.hom = e.hom :=
  sorry

end RingedSite.ModuleDerived.LocallyGiven
