/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
import StacksCheckRecall

/-!
# Lemma 18.32.2

The equivalence criterion and flatness live at the monoidal-category layer.  The finite
presentation, local retract, and duality consequences live at the generic ringed-site module
layer.  This file is only the typed source facade.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (L : ringedSiteModuleCategory J O)

section TensorInverse

/- Lemma 18.32.2 (1) iff (2) (0B8N): invertibility is equivalent to admitting a right
tensor inverse. -/
@[stacks 0B8N "(1) iff (2)"]
#check
  (MonoidalCategory.isInvertibleObject.tensorRight_iff_exists_rightTensorInverse L :
    (tensorRight L).IsEquivalence ↔
      ∃ N : ringedSiteModuleCategory J O,
        Nonempty (L ⊗ N ≅ 𝟙_ (ringedSiteModuleCategory J O)))

end TensorInverse

/- Lemma 18.32.2, consequence (1) (0B8N): every invertible module sheaf is flat. -/
@[stacks 0B8N "consequence (1), flat"]
#check fun [MonoidalCategory.isInvertibleObject L] ↦
  (CategoryTheory.MonoidalCategory.isFlat_of_isInvertibleObject L : IsFlat O L)

/- Lemma 18.32.2, consequence (1) (0B8N): every invertible module sheaf is finitely presented. -/
section FinitePresentation

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

@[stacks 0B8N "consequence (1), finite presentation"]
#check fun [MonoidalCategory.isInvertibleObject L] ↦
  (isFinitePresentation_of_isInvertible L : L.IsFinitePresentation)

end FinitePresentation

section Retract

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Lemma 18.32.2, consequence (2) (0B8N): every invertible module sheaf is locally a
retract of a finite free module sheaf. -/
@[stacks 0B8N "consequence (2)"]
#check fun [MonoidalCategory.isInvertibleObject L] ↦
  (FiniteFreeRetract.isLocal_of_isInvertible L : FiniteFreeRetract.IsLocal L)

end Retract

section Dual

variable [Closed L]
variable (N : ringedSiteModuleCategory J O)
variable (e : L ⊗ N ≅ unitModule J O)

/- Lemma 18.32.2, consequence (3) (0B8N): a specified tensor inverse determines a concrete
isomorphism to the internal-Hom dual. -/
@[stacks 0B8N "consequence (3)"]
#check
  (dual.isoOfTensorInverse L N e : N ≅ dual L)

end Dual

end SheafOfModules.RingedSite
