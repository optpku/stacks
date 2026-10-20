/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_18_1_Cartesian
public import stacks_project.Chap85.Lemma_85_23_3_Fiberwise

/-!
# Total fiberwise Serre subcategory of a hypercovering

The weak Serre subcategory `A_total ⊂ Mod(O)` of cartesian `O`-modules on
`((C / K)_total, O)` whose degree-`n` restrictions lie in `A_{K_n}`, together with the
transported bounded-cohomology basis on the total site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open RingedSite
open RingedSite.Hom
open RingedSite.Localization
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι wι u v w

namespace RingedSite.FiberwiseSerre

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap
    overIncl)

open RingedSite.Localization.AtSimplicialSR
open RingedSite.Localization.AtSR

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ {U V : X} (f : V ⟶ U),
    (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]
variable (A : FiberwiseSerre.{wι, u, v, w} X)
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))
variable [UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
    (totalForget K).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w} (toAmbient K).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w} (stageIncl K n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (stageMap K φ).structureMap).IsRightAdjoint]

/-- The weak Serre subcategory `A_total ⊂ Mod(O)` of cartesian `O`-modules whose restriction
`F_n` lies in `A_{K_n}` for every `n`. -/
def total : ObjectProperty (ModuleCat.{w} (site K)) :=
  fun F ↦ cartesianProperty K F ∧
    ∀ n : SimplexCategory, A.atSR (K.obj (op n)) ((moduleComponent K n).obj F)

/-- Membership in `A_total` is cartesianness together with `F_n ∈ A_{K_n}` for every `n`. -/
theorem mem_total_iff (F : ModuleCat.{w} (site K)) :
    A.total K F ↔
      cartesianProperty K F ∧
        ∀ n : SimplexCategory, A.atSR (K.obj (op n)) ((moduleComponent K n).obj F) :=
  sorry

/-- The subcategory `A_total` is a weak Serre subcategory of `Mod(O)`. -/
instance total_isWeakSerreClass : IsWeakSerreClass (A.total K) :=
  sorry

/-- Inverse image `a^*` sends the global subcategory `A` into `A_total`. -/
theorem modulePullback_maps_global :
    A.global ≤ (A.total K).inverseImage (toAmbient K).modulePullback :=
  sorry

/-- Direct image `a_*` sends `A_total` into the global subcategory `A`. -/
theorem modulePushforward_maps_total :
    A.total K ≤ A.global.inverseImage (toAmbient K).modulePushforward :=
  sorry

/-- Identity-degree fiber object over the same `U_{n,i}` as `x`, with structure map
`f` followed by the structure map of `x`. -/
def identityDegreeFiber (x : Grothendieck (overSiteDiagram K))
    {W : X.carrier} (f : W ⟶ (totalForget K).obj x) :
    Over ((K.obj x.base).obj x.fiber.fst) :=
  Over.mk (f ≫ eqToHom rfl ≫ x.fiber.snd.hom)

/-- The underlying object of `identityDegreeFiber x f` is the source of `f`. -/
theorem identityDegreeFiber_left (x : Grothendieck (overSiteDiagram K))
    {W : X.carrier} (f : W ⟶ (totalForget K).obj x) :
    (identityDegreeFiber K x f).left = W :=
  sorry

/-- Identity-degree lift of a morphism into `totalForget.obj x` to an object of `Over x`. -/
def identityDegreeOver (x : Grothendieck (overSiteDiagram K))
    {W : X.carrier} (f : W ⟶ (totalForget K).obj x) : Over x :=
  Over.mk
    ((Grothendieck.ι (overSiteDiagram K) x.base).map
      ((overIncl (K.obj x.base) x.fiber.fst).map
        (Over.homMk (f ≫ eqToHom rfl) :
          identityDegreeFiber K x f ⟶ x.fiber.snd)))

/-- The source of `identityDegreeOver x f` forgets to the source of `f`. -/
theorem identityDegreeOver_left (x : Grothendieck (overSiteDiagram K))
    {W : X.carrier} (f : W ⟶ (totalForget K).obj x) :
    (totalForget K).obj (identityDegreeOver K x f).left = W :=
  sorry

/-- Identity-degree transport of a covering of `totalForget.obj x` to a covering of `x`. -/
def identityDegreeCover (x : Grothendieck (overSiteDiagram K))
    (cover : FormalCoproduct.{wι} (Over ((totalForget K).obj x))) :
    FormalCoproduct.{wι} (Over x) where
  I := cover.I
  obj i := identityDegreeOver K x (cover.obj i).hom

/-- Identity-degree transport preserves the covering index type. -/
theorem identityDegreeCover_I (x : Grothendieck (overSiteDiagram K))
    (cover : FormalCoproduct.{wι} (Over ((totalForget K).obj x))) :
    (identityDegreeCover K x cover).I = cover.I :=
  sorry

/-- The transported Situation 21.25.1 covering data on `(C / K)_total`: objects whose image
under `totalForget` lies in `B`, with bounds and identity-degree coverings copied from the
underlying objects. -/
def totalBoundedCohomologyBasis :
    FiberwiseSerre.BoundedCohomology.{wι, max ι u v, max ι u v, w} (site K) where
  basis := {x | (totalForget K).obj x ∈ A.bounded.basis}
  hasEnoughObjectsWithProperty := sorry
  cohomologyBound {x} hx := A.bounded.cohomologyBound hx
  coveringSystem {x} hx :=
    Set.image (identityDegreeCover K x) (A.bounded.coveringSystem hx)
  coveringSystemIsCover := sorry
  coveringSystemCofinal := sorry

/-- The total-site basis consists of objects whose image under `totalForget` lies in `B`. -/
theorem totalBoundedCohomologyBasis_basis :
    (A.totalBoundedCohomologyBasis K).basis =
      {x | (totalForget K).obj x ∈ A.bounded.basis} :=
  sorry

end RingedSite.FiberwiseSerre

end
