module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Algebra.Category.Ring.Sheaf.Units
import StacksCheckRecall

/-!
# Definition 18.32.1

Fixed rank, tensor-invertibility, and the units sheaf have independent reusable owners.  This
entry records the three source clauses without rebuilding any of them in the chapter namespace.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O : Sheaf J CommRingCat.{max u v}}

section Rank

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (r : ℕ) (F : RingedSite.ringedSiteModuleCategory J O)

/- Definition 18.32.1 (1) (0409): finite locally free module sheaves of constant rank `r`. -/
@[stacks 0409 "(1)"]
#check (IsFiniteLocallyFreeOfRank r F : Prop)

end Rank

section Invertible

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (L : RingedSite.ringedSiteModuleCategory J O)

/- Definition 18.32.1 (2) (0409): invertibility is the canonical invertible-object property;
the generic bridge identifies it with equivalence of right tensoring as in the source. -/
@[stacks 0409 "(2)"]
#check
  (MonoidalCategory.isInvertibleObject.iff_tensorRight L :
    MonoidalCategory.isInvertibleObject L ↔ (tensorRight L).IsEquivalence)

end Invertible

/- Definition 18.32.1 (3) (0409): the commutative-group-valued sheaf of invertible local
sections. -/
@[stacks 0409 "(3)"]
#check (CategoryTheory.Sheaf.unitsSheaf O : Sheaf J CommGrpCat)

end SheafOfModules
