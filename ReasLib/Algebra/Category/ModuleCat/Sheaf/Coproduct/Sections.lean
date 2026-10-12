/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Topology.LocallyFinite
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.CategoryTheory.Functor.SectionsTerminal
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.Topology.Sheaves.Glue
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally finite sections of coproducts of sheaves of modules

A section of an infinite coproduct need not be a globally finite sum.  A locally finite family of
component sections does, however, determine a section: on every sufficiently small open set only
finitely many components remain, and these finite sums glue.  This file provides that construction
and its specialization to morphisms between free sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {𝒪 : X.Sheaf RingCat.{u}}

namespace SectionFamily

variable {ι : Type u} (M : ι → SheafOfModules.{u} 𝒪) (s : ∀ i, (M i).sections)
variable [HasCoproduct M]

/-- Opens meeting the supports of only finitely many sections in a family. -/
def FiniteOpen :=
  {U : Opens X // {i | (sectionSupport (s i) ∩ (U : Set X)).Nonempty}.Finite}

namespace FiniteOpen

/-- The open subset underlying a finite-support open. -/
abbrev toOpens (U : FiniteOpen M s) : Opens X := U.1

/-- The canonical inclusion of a finite-support open into the whole space. -/
def toTop (U : FiniteOpen M s) : U.toOpens ⟶ (⊤ : Opens X) :=
  homOfLE le_top

/-- The finite set of components whose support meets a finite-support open. -/
noncomputable def active (U : FiniteOpen M s) : Finset ι :=
  U.2.toFinset

/-- A component is active exactly when its support meets the open. -/
@[simp]
theorem mem_active_iff (U : FiniteOpen M s) (i : ι) :
    i ∈ U.active ↔ (sectionSupport (s i) ∩ (U.toOpens : Set X)).Nonempty := sorry

end FiniteOpen

/-- A locally finite family of supports is covered by its finite-support opens. -/
theorem finiteOpen_cover
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    (⊤ : Opens X) ≤ ⨆ U : FiniteOpen M s, U.toOpens := sorry

/-- The finite sum of the component sections on a finite-support open. -/
noncomputable def localSum (U : FiniteOpen M s) :
    ((∐ M).val.obj (op U.toOpens)) :=
  ∑ i ∈ U.active, (sectionsMap (Sigma.ι M i) (s i)).val (op U.toOpens)

/-- The local finite sums agree on overlaps. -/
theorem localSum_compatible :
    TopCat.Presheaf.IsCompatible ((toSheaf 𝒪).obj (∐ M)).obj
      (fun U : FiniteOpen M s ↦ U.toOpens) (localSum M s) := sorry

/-- The value on the whole space obtained by gluing the local finite sums. -/
noncomputable def gluedTopSection
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    ((∐ M).val.obj (op (⊤ : Opens X))) :=
  TopCat.Sheaf.glueOfCompatibleFamily
    ((toSheaf 𝒪).obj (∐ M) : X.Sheaf AddCommGrpCat.{u})
    (fun U : FiniteOpen M s ↦ U.toOpens) ⊤ (fun U ↦ U.toTop)
    (finiteOpen_cover M s hs) (localSum M s) (localSum_compatible M s)

/-- A locally finite family of component sections determines a section of their coproduct. -/
@[stacks 01BL "locally finite coproduct section"]
noncomputable def toCoproduct
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    (∐ M).sections :=
  (CategoryTheory.Functor.sectionsEquivTerminal
    ((∐ M).val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) ⊤ isTerminalTop).symm
      (gluedTopSection M s hs)

/-- On a finite-support open, the locally finite coproduct section is the expected finite sum. -/
theorem toCoproduct_eval_finiteOpen
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (U : FiniteOpen M s) :
    (toCoproduct M s hs).val (op U.toOpens) = localSum M s U := sorry

/-- On any open with a specified finite set of active components, the locally finite coproduct
section is the corresponding finite sum. -/
theorem toCoproduct_eval
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (U : Opens X) (t : Finset ι)
    (ht : ∀ i, (sectionSupport (s i) ∩ (U : Set X)).Nonempty → i ∈ t) :
    (toCoproduct M s hs).val (op U) =
      ∑ i ∈ t, (sectionsMap (Sigma.ι M i) (s i)).val (op U) := sorry

/-- Projecting a locally finite coproduct section to one summand recovers that component. -/
@[simp]
theorem project_toCoproduct [DecidableEq ι]
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (i : ι) :
    sectionsMap (Sigma.π M i) (toCoproduct M s hs) = s i := sorry

end SectionFamily

namespace Free

/-- The canonical projection from a free sheaf to one copy of its coefficient sheaf. -/
noncomputable def projection {ι : Type u} [DecidableEq ι] (i : ι) :
    free (R := 𝒪) ι ⟶ unit 𝒪 :=
  Sigma.π (fun _ : ι ↦ unit 𝒪) i

/-- Projecting a section after injectively reindexing its free basis recovers the original
coordinate. -/
@[stacks 01BL "injective free-section reindexing"]
theorem project_freeMap_same {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]
    (e : ι → κ) (he : Function.Injective e)
    (s : (free (R := 𝒪) ι).sections) (i : ι) :
    sectionsMap (projection (e i)) (sectionsMap (freeMap (R := 𝒪) e) s) =
      sectionsMap (projection i) s := sorry

/-- A coordinate outside the range of a free-basis reindexing vanishes on every reindexed
section. -/
@[stacks 01BL "free-section coordinate outside the reindexing range"]
theorem project_freeMap_eq_zero {ι κ : Type u} [DecidableEq κ]
    (e : ι → κ) (s : (free (R := 𝒪) ι).sections) (k : κ)
    (hk : k ∉ Set.range e) :
    sectionsMap (projection k) (sectionsMap (freeMap (R := 𝒪) e) s) = 0 := sorry

/-- A locally finite family of scalar sections determines a section of a free sheaf. -/
@[stacks 01BL "locally finite free section"]
noncomputable def sectionOfLocallyFinite {ι : Type u}
    (s : ι → (unit 𝒪).sections)
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) :
    (free (R := 𝒪) ι).sections :=
  SectionFamily.toCoproduct (fun _ ↦ unit 𝒪) s hs

/-- Projecting a locally finite section of a free sheaf recovers its chosen coefficient. -/
@[simp]
theorem project_sectionOfLocallyFinite {ι : Type u} [DecidableEq ι]
    (s : ι → (unit 𝒪).sections)
    (hs : LocallyFinite fun i ↦ sectionSupport (s i)) (i : ι) :
    sectionsMap (projection i) (sectionOfLocallyFinite s hs) = s i := sorry

/-- A componentwise locally finite coefficient family determines a morphism between free sheaves. -/
@[stacks 01BL "locally finite free sheaf morphism"]
noncomputable def homOfLocallyFinite {ι κ : Type u}
    (a : ι → κ → (unit 𝒪).sections)
    (ha : ∀ i, LocallyFinite fun k ↦ sectionSupport (a i k)) :
    free (R := 𝒪) ι ⟶ free (R := 𝒪) κ :=
  (freeHomEquiv (free (R := 𝒪) κ)).symm
    (fun i ↦ sectionOfLocallyFinite (a i) (ha i))

/-- Evaluating `homOfLocallyFinite` on a basis vector gives its locally finite coefficient
family. -/
theorem freeHomEquiv_homOfLocallyFinite {ι κ : Type u}
    (a : ι → κ → (unit 𝒪).sections)
    (ha : ∀ i, LocallyFinite fun k ↦ sectionSupport (a i k)) (i : ι) :
    freeHomEquiv (free (R := 𝒪) κ) (homOfLocallyFinite a ha) i =
      sectionOfLocallyFinite (a i) (ha i) := sorry

end Free

end SheafOfModules
