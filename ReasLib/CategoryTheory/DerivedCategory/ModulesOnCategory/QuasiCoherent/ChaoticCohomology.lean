module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.WeakSerre
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherent derived modules on a flat chaotic ringed site

Flat restriction maps identify the canonical derived base-change condition with
quasi-coherence of every cohomology module sheaf.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.ModulesOnCategory.Chaotic

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C)
  CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]
variable [∀ U : C, HasWeakSheafify
  ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat.{max (max u v) w}]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective
  AddCommGrpCat.{max (max u v) w}]
variable [Presheaf.Restriction.Flat O.obj]

/-- If every restriction morphism of `O` is flat, then the canonical quasi-coherence
property on derived `O`-modules is exactly the property that every cohomology module sheaf
is quasicoherent. -/
@[stacks 0GZR]
theorem isQuasiCoherent_eq_cohomologyIn :
    isQuasiCoherent O =
      @DerivedCategory.cohomologyIn _ inferInstance inferInstance
        (RingedSite.Hom.moduleCat_hasDerivedCategory
          (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) O))
        (SheafOfModules.isQuasicoherent
          (SheafOfModules.RingedSite.ringSheaf
            (⊥ : GrothendieckTopology C) O)) := sorry

/-- A derived module on a flat chaotic ringed site is canonically quasi-coherent exactly
when each of its cohomology module sheaves is quasicoherent. -/
@[simp, stacks 0GZR "objectwise membership"]
theorem mem_iff_cohomology_isQuasicoherent
    (K : RingedSite.Hom.ModuleDerived.{max (max u v) w}
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) O)) :
    isQuasiCoherent O K ↔
      ∀ n : ℤ,
        SheafOfModules.isQuasicoherent
          (SheafOfModules.RingedSite.ringSheaf
            (⊥ : GrothendieckTopology C) O)
          ((@DerivedCategory.homologyFunctor _ inferInstance inferInstance
            (RingedSite.Hom.moduleCat_hasDerivedCategory
              (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) O)) n).obj K) := sorry

end CategoryTheory.ModulesOnCategory.Chaotic
