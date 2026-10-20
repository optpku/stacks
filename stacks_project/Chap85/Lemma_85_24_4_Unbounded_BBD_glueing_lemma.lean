/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import stacks_project.Chap85.Lemma_85_24_2_System
public import stacks_project.Chap85.Lemma_85_24_3_BBD_glueing_lemma_Solution
public import stacks_project.Chap85.Lemma_85_24_4_Unbounded_BBD_glueing_lemma_Cohomology

/-!
# Lemma 85.24.4 (Unbounded BBD glueing lemma)

In Situation 85.24.1, the same site-morphism and full-subcategory covering
hypotheses as the bounded BBD glueing lemma, vanishing of negative self-Exts
of each `E_U`, and a fiberwise weak Serre family `A_U` on `C` with `E_U` in
`D_{A_{u(U)}}(O_{u(U)})`, produce a solution unique up to unique compatible
isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite
open RingedSite.Hom
open RingedSite.Localization
open RingedSite.ModuleDerived
open RingedSite.ModuleDerived.LocallyGiven
open scoped SemiRepresentableFamily

noncomputable section

universe ιfam wι u v w uB vB u' v'

namespace RingedSite.ModuleDerived.LocallyGiven

variable {X : RingedSite.{u, v, w}}
variable [h_eqX : HasEqualizers X.carrier] [h_pbX : HasPullbacks X.carrier]
variable {B : Type uB} [Category.{vB} B]
variable [h_univLE : UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ {U V : X} (f : V ⟶ U),
    (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]
variable (D : @LocallyGiven.{u, v, w, w, uB, vB} h_univLE X B inferInstance)
variable {C' : Type u'} [Category.{v'} C']
variable [h_eqC : HasEqualizers C'] [h_pbC : HasPullbacks C']
variable (J' : GrothendieckTopology C') (u' : C' ⥤ X)
variable [h_sites : IsMorphismOfSites J' X.siteTopology u']
variable [h_eqPres : PreservesLimitsOfShape WalkingParallelPair u']
variable [h_pbPres : PreservesLimitsOfShape WalkingCospan u']
variable (ι : B ⥤ C') [h_full : ι.Full] [h_faithful : ι.Faithful]
variable (A : FiberwiseSerre.{wι, u, v, w} X)
include h_eqX h_pbX h_eqC h_pbC h_sites h_eqPres h_pbPres h_full h_faithful

/-- Lemma 85.24.4 (Unbounded BBD glueing lemma) (1)
In Situation 85.24.1, assume `C` and an auxiliary site `D` have equalizers and
fibre products, a morphism of sites `C → D` is given by a continuous functor
`u' : D ⥤ C` preserving those limits, `B` is a full subcategory of `D` with
`LocallyGiven.u` the restriction of `u'`, every object of `D` admits a covering
by objects of `B`, negative self-Exts of each `E_U` vanish, and there is a
fiberwise weak Serre family `A_U` with each `E_U` of cohomology in
`A.property` at `u(U)`. Then a solution exists. -/
@[stacks 0DCC]
theorem exists_solution_of_cohomologyIn
    (h_restrict : D.u = ι ⋙ u')
    (h_cover : ∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj))
    (h_neg : negativeSelfExt h_univLE D)
    (h_mem : obj_mem_cohomologyIn D A) :
    Nonempty (Solution D) :=
  sorry

/-- Lemma 85.24.4 (Unbounded BBD glueing lemma) (2)
In the situation of Lemma 85.24.4 (Unbounded BBD glueing lemma) (1), a solution
is unique up to a unique isomorphism of global objects compatible with the
identifications `ρ_U`. -/
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
