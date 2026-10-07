module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Vanishing
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology
public import ReasLib.CategoryTheory.Sites.Cech.Refinement
public import ReasLib.Topology.Opens.Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinal basis systems for module Čech cohomology

This leaf owns the basiswise covering predicate used to pass from Čech acyclicity on a
cofinal family of covers to ordinary sheaf cohomology.  It contains no Chapter import:
the covering/refinement data are topological, while the vanishing payload is the canonical
module-valued Čech cohomology object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace ModuleCech

/- The basis-membership and vanishing clauses are independent of the cofinality quantifiers.  Keep
  them as small predicates so that other Cech constructions can reuse the same hypotheses. -/

/-- An indexed family of opens is stable under the chosen basis when every member and every
nonempty finite intersection belongs to `B`.  The member condition is retained explicitly even
though the one-index intersections already recover it. -/
@[stacks 01EW "basis-stable indexed open family"]
def IsBasisStableFamily
    (B : Set (Opens X.carrier)) {ι : Type v} (𝒰 : ι → Opens X.carrier) : Prop :=
  (∀ i, 𝒰 i ∈ B) ∧
    ∀ (p : ℕ) (σ : Fin (p + 1) → ι), iInf (𝒰 ∘ σ) ∈ B

namespace IsBasisStableFamily

/-- Every member of a basis-stable family lies in the basis. -/
@[stacks 01EW "basis-stable family membership"]
theorem mem
    {B : Set (Opens X.carrier)} {ι : Type v} {𝒰 : ι → Opens X.carrier}
    (h𝒰 : IsBasisStableFamily B 𝒰) (i : ι) : 𝒰 i ∈ B := sorry

/-- Every nonempty finite intersection of a basis-stable family lies in the basis. -/
@[stacks 01EW "basis-stable family finite intersections"]
theorem intersection_mem
    {B : Set (Opens X.carrier)} {ι : Type v} {𝒰 : ι → Opens X.carrier}
    (h𝒰 : IsBasisStableFamily B 𝒰) (p : ℕ) (σ : Fin (p + 1) → ι) :
    iInf (𝒰 ∘ σ) ∈ B := sorry

end IsBasisStableFamily

/-- Positive-degree module-valued Čech cohomology vanishes for an indexed open family. -/
@[stacks 01EW "module Cech acyclicity of an indexed family"]
def IsCechAcyclicFamily
    {ι : Type u} (𝒰 : ι → Opens X.carrier) (ℱ : X.Modules) : Prop :=
  ∀ (p : ℕ), 0 < p → IsZero (moduleCechCohomology 𝒰 ℱ p)

namespace IsCechAcyclicFamily

/-- A family-level acyclicity certificate gives vanishing in every positive degree. -/
@[stacks 01EW "familywise Cech vanishing"]
theorem isZero
    {ι : Type u} {𝒰 : ι → Opens X.carrier} {ℱ : X.Modules}
    (h𝒰 : IsCechAcyclicFamily 𝒰 ℱ) {p : ℕ} (hp : 0 < p) :
    IsZero (moduleCechCohomology 𝒰 ℱ p) := sorry

end IsCechAcyclicFamily

namespace IsAcyclic

/-- A globally Cech-acyclic module is Cech-acyclic on each fixed indexed family. -/
@[stacks 01EV "global-to-family Cech acyclicity"]
theorem isCechAcyclicFamily
    {ℱ : X.Modules} (hℱ : IsAcyclic ℱ)
    {ι : Type u} (𝒰 : ι → Opens X.carrier) :
    IsCechAcyclicFamily 𝒰 ℱ := sorry

/-- The global Cech-acyclicity predicate is equivalent to its familywise formulation. -/
@[stacks 01EV "familywise characterization of Cech acyclicity"]
theorem iff_forall_isCechAcyclicFamily
    (ℱ : X.Modules) :
    IsAcyclic ℱ ↔
      ∀ {ι : Type u} (𝒰 : ι → Opens X.carrier), IsCechAcyclicFamily 𝒰 ℱ := sorry

end IsAcyclic

/-- A module is Čech-acyclic on a basis when every cover of a basis open admits a refinement
whose members and all nonempty finite intersections stay in the basis and whose positive-degree
module-valued Čech cohomology vanishes.  The stability and vanishing clauses are exposed through
`IsBasisStableFamily` and `IsCechAcyclicFamily` for independent reuse. -/
@[stacks 01EW "cofinal basis covers with vanishing higher Cech cohomology"]
def IsAcyclicOnBasis
    (ℱ : X.Modules) (B : Set (Opens X.carrier)) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ B →
    ∀ {κ : Type u} (𝒱 : κ → Opens X.carrier), iSup 𝒱 = U →
        ∃ (ι : Type u) (𝒰 : ι → Opens X.carrier) (refine : ι → κ),
        iSup 𝒰 = U ∧
          IsRefinement 𝒱 𝒰 refine ∧
          IsBasisStableFamily B 𝒰 ∧
          IsCechAcyclicFamily 𝒰 ℱ

namespace IsAcyclicOnBasis

/-- Compatibility characterization of the basiswise predicate in the original expanded
five-field form.  New clients should use `IsBasisStableFamily` and `IsCechAcyclicFamily` directly. -/
@[stacks 01EW "expanded basis Cech acyclicity compatibility"]
theorem iff_expanded
    {B : Set (Opens X.carrier)} {ℱ : X.Modules} :
    IsAcyclicOnBasis ℱ B ↔
      ∀ ⦃U : Opens X.carrier⦄, U ∈ B →
        ∀ {κ : Type u} (𝒱 : κ → Opens X.carrier), iSup 𝒱 = U →
          ∃ (ι : Type u) (𝒰 : ι → Opens X.carrier) (refine : ι → κ),
            iSup 𝒰 = U ∧
              IsRefinement 𝒱 𝒰 refine ∧
              (∀ i, 𝒰 i ∈ B) ∧
              (∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, iInf (𝒰 ∘ σ) ∈ B) ∧
              ∀ p : ℕ, 0 < p → IsZero (moduleCechCohomology 𝒰 ℱ p) := sorry

/-- Extract a basis-stable Čech-acyclic refinement from the canonical predicate. -/
@[stacks 01EW "basis-stable Cech refinement"]
theorem exists_refinement
    {B : Set (Opens X.carrier)} {ℱ : X.Modules}
    (hℱ : IsAcyclicOnBasis ℱ B)
    {U : Opens X.carrier} (hU : U ∈ B)
    {κ : Type u} (𝒱 : κ → Opens X.carrier) (h𝒱 : iSup 𝒱 = U) :
    ∃ (ι : Type u) (𝒰 : ι → Opens X.carrier) (refine : ι → κ),
      iSup 𝒰 = U ∧
        IsRefinement 𝒱 𝒰 refine ∧
        IsBasisStableFamily B 𝒰 ∧
        IsCechAcyclicFamily 𝒰 ℱ := sorry

/-- Compatibility expansion of `exists_refinement` for clients written against the original
five-field conjunction. -/
@[stacks 01EW "expanded basis-stable Cech refinement"]
theorem exists_refinement_expanded
    {B : Set (Opens X.carrier)} {ℱ : X.Modules}
    (hℱ : IsAcyclicOnBasis ℱ B)
    {U : Opens X.carrier} (hU : U ∈ B)
    {κ : Type u} (𝒱 : κ → Opens X.carrier) (h𝒱 : iSup 𝒱 = U) :
    ∃ (ι : Type u) (𝒰 : ι → Opens X.carrier) (refine : ι → κ),
      iSup 𝒰 = U ∧
        IsRefinement 𝒱 𝒰 refine ∧
        (∀ i, 𝒰 i ∈ B) ∧
        (∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, iInf (𝒰 ∘ σ) ∈ B) ∧
        ∀ p : ℕ, 0 < p → IsZero (moduleCechCohomology 𝒰 ℱ p) := sorry

/-- Lemma 20.11.9 (01EW): Čech acyclicity on a cofinal system of basis-stable covers
implies positive-degree sheaf-cohomology vanishing on every basis open. -/
@[stacks 01EW "basiswise cohomology vanishing from cofinal Cech acyclicity"]
theorem isZero_cohomology
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {B : Set (Opens X.carrier)} {ℱ : X.Modules}
    (hℱ : IsAcyclicOnBasis ℱ B) (hB : Opens.IsBasis B)
    {U : Opens X.carrier} (hU : U ∈ B) {p : ℕ} (hp : 0 < p) :
    IsZero (((moduleUnderlyingSheaf X).obj ℱ).H' p U) := sorry

/-- Module-valued companion of `isZero_cohomology`.  The additive theorem above remains the
underlying-sheaf view used by the source recall, while this result is the reusable object-level
statement over `sectionsRingOnOpen X U`. -/
@[stacks 01EW "module-valued basiswise cohomology vanishing"]
theorem isZero_module_cohomology
    {B : Set (Opens X.carrier)} {ℱ : X.Modules}
    (hℱ : IsAcyclicOnBasis ℱ B) (hB : Opens.IsBasis B)
    {U : Opens X.carrier} (hU : U ∈ B) {p : ℕ} (hp : 0 < p) :
    IsZero (moduleCohomologyAtOpen U ℱ p) := sorry

end IsAcyclicOnBasis

end ModuleCech

end AlgebraicGeometry.RingedSpace

end
