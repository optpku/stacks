module

public import stacks_project.Chap85.Situation_85_24_1_LocallyGiven
public import stacks_project.Chap85.Lemma_85_23_3_Fiberwise

/-!
# Cohomology-in membership for locally given objects

A locally given datum has cohomology in a fiberwise weak Serre family when each
`E_U` has cohomology in `A.property` at `u(U)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite
open RingedSite.Hom
open RingedSite.Localization
open RingedSite.ModuleDerived

noncomputable section

universe wι u v w uB vB

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
