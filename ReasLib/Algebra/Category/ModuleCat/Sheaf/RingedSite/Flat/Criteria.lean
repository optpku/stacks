module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local finite-free criteria for flat module sheaves

Flatness on a ringed site admits a local relation-lifting formulation.  The API below separates
the reusable factorization predicate from its rank-one and arbitrary-matrix specializations, and
then supplies direct pairwise equivalences in addition to the textbook `List.TFAE` view.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FlatCriterion

/-- The finite free module sheaf of rank `n` on a commutative ringed site. -/
abbrev FiniteFree {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (O : Sheaf J CommRingCat.{max u v}) (n : ℕ) :
    ringedSiteModuleCategory J O :=
  SheafOfModules.free (ULift.{max u v} (Fin n))

namespace FiniteFree

/-- The finite free module of rank `n` after passing to the iterated slice over `V`. -/
abbrev over {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (O : Sheaf J CommRingCat.{max u v})
    {U : C} (V : Over U)
    [HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
    [((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (n : ℕ) :
    ringedSiteModuleCategory ((J.over U).over V) ((O.over U).over V) :=
  FiniteFree ((J.over U).over V) ((O.over U).over V) n

end FiniteFree

/-- Further restriction from the slice over `U` to the iterated slice over `V`. -/
noncomputable abbrev restriction {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (O : Sheaf J CommRingCat.{max u v}) {U : C} (V : Over U) :
    ringedSiteModuleCategory (J.over U) (O.over U) ⥤
      ringedSiteModuleCategory ((J.over U).over V) ((O.over U).over V) :=
  SheafOfModules.overFunctor ((ringSheaf J O).over U) V

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ (U : C) (V : Over U),
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ (U : C) (V : Over U),
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- A relation among finite free generators of `M` factors locally through a finite free module
on which the relation vanishes. -/
@[stacks 08FC "local factorization"]
def FactorsLocally (M : ringedSiteModuleCategory J O) {U : C} {m n : ℕ}
    (A : FiniteFree (J.over U) (O.over U) m ⟶
      FiniteFree (J.over U) (O.over U) n)
    (s : FiniteFree (J.over U) (O.over U) n ⟶ M.over U) : Prop :=
  ∃ (I : Type u) (Uᵢ : I → Over U), (J.over U).CoversTop Uᵢ ∧
    ∀ i : I,
      ∃ (l : ℕ)
        (B : (restriction J O (Uᵢ i)).obj (FiniteFree (J.over U) (O.over U) n) ⟶
          FiniteFree.over J O (Uᵢ i) l)
        (t : FiniteFree.over J O (Uᵢ i) l ⟶ (M.over U).over (Uᵢ i)),
        (restriction J O (Uᵢ i)).map s = B ≫ t ∧
          (restriction J O (Uᵢ i)).map A ≫ B = 0

/-- The rank-one local relation-factorization criterion for a module sheaf. -/
@[stacks 08FC "single relation"]
def SingleRelation (M : ringedSiteModuleCategory J O) : Prop :=
  ∀ (U : C) (n : ℕ)
    (f : FiniteFree (J.over U) (O.over U) 1 ⟶ FiniteFree (J.over U) (O.over U) n)
    (s : FiniteFree (J.over U) (O.over U) n ⟶ M.over U),
    f ≫ s = 0 → FactorsLocally M f s

/-- The arbitrary finite-matrix local relation-factorization criterion for a module sheaf. -/
@[stacks 08FC "finite matrix"]
def Matrix (M : ringedSiteModuleCategory J O) : Prop :=
  ∀ (U : C) (m n : ℕ)
    (A : FiniteFree (J.over U) (O.over U) m ⟶ FiniteFree (J.over U) (O.over U) n)
    (s : FiniteFree (J.over U) (O.over U) n ⟶ M.over U),
    A ≫ s = 0 → FactorsLocally M A s

/-- Flatness is equivalent to the rank-one local relation-factorization criterion. -/
theorem isFlat_iff_singleRelation (M : ringedSiteModuleCategory J O) :
    IsFlat O M ↔ SingleRelation M := sorry

/-- The rank-one and arbitrary finite-matrix local factorization criteria are equivalent. -/
theorem singleRelation_iff_matrix (M : ringedSiteModuleCategory J O) :
    SingleRelation M ↔ Matrix M := sorry

/-- Flatness is equivalent to the arbitrary finite-matrix local factorization criterion. -/
theorem isFlat_iff_matrix (M : ringedSiteModuleCategory J O) :
    IsFlat O M ↔ Matrix M := sorry

/-- Lemma 18.28.14 (08FC): flatness, the rank-one criterion, and the finite-matrix criterion are
equivalent. -/
@[stacks 08FC]
theorem isFlat_tfae (M : ringedSiteModuleCategory J O) :
    List.TFAE [IsFlat O M, SingleRelation M, Matrix M] := sorry

end SheafOfModules.RingedSite.FlatCriterion
