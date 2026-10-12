/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Top cohomology of a bounded-above quasi-coherent object

This file relates canonical quasi-coherence in the derived category to ordinary
quasi-coherence of the highest potentially nonzero cohomology sheaf.  The canonical
`DerivedCategory.IsLE` formulation is accompanied by the pointwise vanishing formulation used
in the source statement.
-/

@[expose] public section

-- Keep these operations on the already specified canonical derived-category model.
-- Local instance justification (defeq pin): the ringed-site and commutative-ring-sheaf presentations below denote the same standard quotient; enable both existing reducible presentation owners so their Q objects share that model.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory

noncomputable section

-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

open CategoryTheory Limits
open ComplexShape Opposite
open SheafOfModules.RingedSite

universe u v w

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]
variable [∀ X : C, HasWeakSheafify ((⊥ : GrothendieckTopology C).over X)
  AddCommGrpCat.{max (max u v) w}]
variable [∀ X : C, ((⊥ : GrothendieckTopology C).over X).WEqualsLocallyBijective
  AddCommGrpCat.{max (max u v) w}]

/-- If a canonically quasi-coherent derived module is bounded above by `b`, then its degree-`b`
cohomology sheaf is quasi-coherent.  This is the canonical t-structure formulation of
Lemma 21.43.3. -/
@[stacks 0GZQ "bounded-above formulation"]
theorem topCohomology_isQuasicoherent_of_isLE
    (K : Chaotic.QC 𝒪)
    (b : ℤ) (hK : K.obj.IsLE b) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{max (max u v) w}
        (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) b).obj
        K.obj).IsQuasicoherent :=
  sorry

/-- Lemma 21.43.3 (0GZQ): if `K` is canonically quasi-coherent and
`(DerivedCategory.homologyFunctor _ i).obj K` is zero for every `i > b`, then its degree-`b`
cohomology is a quasi-coherent module sheaf. -/
@[stacks 0GZQ]
theorem topCohomology_isQuasicoherent
    (K : Chaotic.QC 𝒪)
    (b : ℤ)
    (hvanish : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{max (max u v) w}
          (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) i).obj K.obj)) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{max (max u v) w}
        (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) b).obj
        K.obj).IsQuasicoherent :=
  sorry

end CategoryTheory.ModulesOnCategory
