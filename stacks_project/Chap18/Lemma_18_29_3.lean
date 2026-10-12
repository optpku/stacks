/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Flat
import StacksCheckRecall

/-!
# Lemma 18.29.3

Compatibility facade for the local finite-free retract criterion for flat finitely presented
module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (M : ringedSiteModuleCategory J 𝒪)
variable [M.IsFinitePresentation] [IsFlat 𝒪 M]

/- Lemma 18.29.3 (08FD): a flat finitely presented module sheaf is locally a finite-free
retract. -/
@[stacks 08FD]
#check (FiniteFreeRetract.IsLocal.ofIsFinitePresentationOfFlat M :
  FiniteFreeRetract.IsLocal M)

/- The reusable predicate exposes the source's covering and split-map formulation. -/
#check (FiniteFreeRetract.isLocal_iff_split M :
  FiniteFreeRetract.IsLocal M ↔
    ∀ U : C,
      ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
        ∀ i : I,
          ∃ α : Type (max u v), Finite α ∧
            ∃ ι :
                (M.over U).over (Ui i) ⟶
                  (SheafOfModules.free α :
                    ringedSiteModuleCategory ((J.over U).over (Ui i))
                      ((𝒪.over U).over (Ui i))),
              ∃ π :
                  (SheafOfModules.free α :
                    ringedSiteModuleCategory ((J.over U).over (Ui i))
                      ((𝒪.over U).over (Ui i))) ⟶
                    (M.over U).over (Ui i),
                ι ≫ π = 𝟙 ((M.over U).over (Ui i)))

end SheafOfModules.RingedSite
