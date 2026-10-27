/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Complex
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.MorphismProperty.IsPreservedBy
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of K-flat complexes on ringed sites

For commutative ringed-site presentations, degreewise module pullback preserves termwise
flatness and K-flatness, with no local additive or monoidal instance reconstruction.  The
underlying complex functor is owned independently by `Pullback.Complex`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.modulePushforward.{w}).IsRightAdjoint]

namespace modulePullbackComplex

/-- Module pullback preserves termwise flatness of cochain complexes. -/
@[stacks 0G7E "termwise flatness"]
theorem isTermwiseFlat
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hK : HomologicalComplex.IsTermwiseFlat K) :
    HomologicalComplex.IsTermwiseFlat ((modulePullbackComplex f).obj K) := sorry

/-- Module pullback preserves K-flatness for a K-flat complex with flat terms. -/
@[stacks 0G7E "K-flatness"]
theorem isKFlat_of_isTermwiseFlat
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hKFlat : K.IsKFlat) (hK : HomologicalComplex.IsTermwiseFlat K) :
    ((modulePullbackComplex f).obj K).IsKFlat := sorry

/-- Module pullback preserves K-flat complexes with flat terms. -/
@[stacks 0G7E]
theorem isKFlat_and_isTermwiseFlat
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hKFlat : K.IsKFlat) (hK : HomologicalComplex.IsTermwiseFlat K) :
    ((modulePullbackComplex f).obj K).IsKFlat ∧
      HomologicalComplex.IsTermwiseFlat ((modulePullbackComplex f).obj K) :=
  ⟨isKFlat_of_isTermwiseFlat f K hKFlat hK, isTermwiseFlat f K hK⟩

/-- Module pullback preserves the canonical object property of K-flat cochain complexes with
flat terms. This is the reusable universal-pullback interface for underlying complexes; it does
not assert relative flatness over a differential graded algebra. -/
@[stacks 0G7E "K-flat termwise-flat object property"]
theorem termwiseFlat
    (K : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ)
    (hK : HomologicalComplex.KFlat.termwiseFlat (ComplexShape.up ℤ) K) :
    HomologicalComplex.KFlat.termwiseFlat (ComplexShape.up ℤ)
      ((modulePullbackComplex f).obj K) :=
  isKFlat_and_isTermwiseFlat f K hK.1 hK.2

variable [CategoryWithHomology (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))]
variable [CategoryWithHomology (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))]

/-- Pullback preserves a quasi-isomorphism between K-flat complexes with flat terms.  Both
endpoint hypotheses are essential on a general ringed site. -/
@[stacks 06YY "good quasi-isomorphisms"]
theorem map_quasiIso
    {K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ℤ}
    (hK : K.IsKFlat) (hK' : HomologicalComplex.IsTermwiseFlat K)
    (hL : L.IsKFlat) (hL' : HomologicalComplex.IsTermwiseFlat L)
    (α : K ⟶ L) (hα : QuasiIso α) :
    QuasiIso ((modulePullbackComplex f).map α) := sorry

end modulePullbackComplex

namespace modulePullbackHomotopy

/-- Pullback carries a K-flat homotopy complex with flat terms to another such good model. -/
@[stacks 0G7E "pullback preserves good models"]
theorem termwiseFlat
    {K : HomotopyCategory
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) (ComplexShape.up ℤ)}
    (hK : HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) K) :
    HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))
      ((modulePullbackHomotopy f).obj K) :=
  modulePullbackComplex.termwiseFlat f K.as hK

/-- Module pullback restricted to the reusable full subcategories of K-flat homotopy objects
with flat terms. Its underlying objects and morphisms are ordinary homotopy-level pullback. -/
@[stacks 0G7E "pullback on good flat models"]
def goodModels :
    HomotopyCategory.KFlat.TermwiseFlat
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)) ⥤
      HomotopyCategory.KFlat.TermwiseFlat
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX)) :=
  ObjectProperty.FullSubcategory.restrict (modulePullbackHomotopy f)
    (fun _ hK ↦ termwiseFlat f hK)

namespace goodModels

/-- Forgetting the restricted pullback on good flat models recovers ordinary homotopy-level
pullback after the source inclusion. -/
@[stacks 0G7E "good-model pullback inclusion comparison"]
def compιIso :
    goodModels f ⋙
        (HomotopyCategory.KFlat.termwiseFlat
          (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))).ι ≅
      (HomotopyCategory.KFlat.termwiseFlat
          (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))).ι ⋙
        modulePullbackHomotopy f :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (P := HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY)))
    (Q := HomotopyCategory.KFlat.termwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX)))
    (modulePullbackHomotopy f) (fun _ hK ↦ termwiseFlat f hK)

/-- The underlying object of good-model pullback is ordinary homotopy-level pullback. -/
@[simp]
theorem obj_obj
    (K : HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))) :
    ((goodModels f).obj K).obj = (modulePullbackHomotopy f).obj K.obj := rfl

/-- The underlying morphism of good-model pullback is ordinary homotopy-level pullback. -/
@[simp]
theorem map_hom
    {K L : HomotopyCategory.KFlat.TermwiseFlat
      (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))} (α : K ⟶ L) :
    ((goodModels f).map α).hom = (modulePullbackHomotopy f).map α.hom := rfl

variable [CategoryWithHomology
  (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))]
variable [CategoryWithHomology
  (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))]

/-- Good-model pullback maps restricted quasi-isomorphisms to restricted
quasi-isomorphisms. -/
@[stacks 06YY "pullback preserves good quasi-isomorphisms"]
theorem map_quasiIso :
    (HomotopyCategory.KFlat.TermwiseFlat.quasiIso
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JY OY))).IsMappedBy
      (goodModels f)
      (HomotopyCategory.KFlat.TermwiseFlat.quasiIso
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf JX OX))) := by
  constructor
  rintro ⟨⟨K⟩, hK⟩ ⟨⟨L⟩, hL⟩ α hα
  change HomotopyCategory.quasiIso _ _ α.hom at hα
  change HomotopyCategory.quasiIso _ _ ((modulePullbackHomotopy f).map α.hom)
  have hα' : QuasiIso α.hom.out := by
    apply (HomotopyCategory.quotient_map_mem_quasiIso_iff α.hom.out).mp
    rw [HomotopyCategory.quotient_map_out α.hom]
    exact hα
  have hmap : QuasiIso ((modulePullbackComplex f).map α.hom.out) :=
    modulePullbackComplex.map_quasiIso f hK.1 hK.2 hL.1 hL.2 _ hα'
  rw [← HomotopyCategory.quotient_map_out α.hom]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hmap

end goodModels

end modulePullbackHomotopy
end RingedSite.Hom
